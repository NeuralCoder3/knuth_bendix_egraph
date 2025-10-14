mod kbo;
mod term_rewrite;
mod types;
mod util;
mod p_parser;

use bimap::BiMap;
use clap::Parser;
use fxhash::FxHashSet as HashSet;
use fxhash::FxHashMap as HashMap;
use priority_queue::PriorityQueue;
use std::cmp::Reverse;
use std::io::stdout;
use std::io::Write;
use symbol_table::GlobalSymbol;

use crate::kbo::*;
use crate::term_rewrite::*;
use crate::types::*;

// Twee:
// R: rules & equations (active)
// Q: unprocessed critical pairs (passive)
//   save only overlap position
// J: ground joinable equations for checks
// 


// first implement KBC, then implement twee things
// do not compute CPs if parents no longer in E/R
// flat term
// only sometimes reduce R with respect to each other



/*
first all in Q,
take rule, orient (if possible), add to R/E
compute critical pair, add to Q
simplify R/E with each other
*/



#[cfg(not(feature = "hotpath"))]
macro_rules! measure_block {
    ($name:expr, $block:expr) => {
        $block
    };
}
#[cfg(feature = "hotpath")]
macro_rules! measure_block {
    ($name:expr, $block:expr) => {
        hotpath::measure_block!($name, $block)
    };
}

fn knuth_steps<F>(verbose: bool, lpo: &F, state: (StagedVec<Rule>, StagedVec<Equation>)) -> (bool,(StagedVec<Rule>, StagedVec<Equation>))
where
    F: Fn(&Term, &Term) -> bool,
{
    // Orient, Compose, collapse => if orientable and new rule used
    // simplify, remove trivial => always
    let orient_result = orient_equation(lpo, state);

    if orient_result.is_left() {
        let oriented = orient_result.left().unwrap();
        let composed = compose(oriented);
        // println!("Composed:");
        // printrule(&composed.0);
        // printrules(&composed.1);
        // printeqs(&composed.2);
        // TODO: collapse is wrong
        // let collapsed = collapse(composed);
        // println!("Collapsed:");
        // printrule(&collapsed.0);
        // printrules(&collapsed.1);
        // printeqs(&collapsed.2);
        // let added = add_rule(collapsed);
        let added = add_rule(composed);
        let simplified = simplify(added);
        let removed = remove_trivial(verbose, simplified);
        (true, removed)
    } else {
        let state = orient_result.right().unwrap();
        let copy = state.clone();
        let simplified = simplify(state);
        let removed = remove_trivial(verbose, simplified);
        let changed = removed != copy;
        (changed, removed)
    }
}

fn knuth_loop_staged<F>(verbose: bool, lpo: &F, state: (StagedVec<Rule>, StagedVec<Equation>)) -> (StagedVec<Rule>, StagedVec<Equation>)
where
    F: Fn(&Term, &Term) -> bool,
{
    let mut changed = true;
    let mut new_state = state;
    while changed {
        // println!("\n  Knuth-Bendix step:");
        // println!("Rules:");
        // printrules(&new_state.0);
        // println!("Equations:");
        // printeqs(&new_state.1);

        let (changed_prime, new_state_prime) = knuth_steps(verbose, lpo, new_state);
        changed = changed_prime;
        new_state = new_state_prime;
        // if new_state != new_state_prime {
        //     changed = true;
        //     new_state = new_state_prime;
        // }
    }
    println!();
    new_state
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ENode {
    label: GlobalSymbol,
    children: Vec<Id>,
}

type Id = usize;

#[allow(non_snake_case)]
struct KBEDAG {
    C: BiMap<Id, ENode>, // can be done as Vec<ENode> with id as index, and an additional C_inv
    id_count: usize,
    // replacement_set: old_id -> new_id (old_id no longer exists in C)
    S: HashMap<Id, Id>, // used to keep track of replacements
}


#[allow(non_snake_case)]
struct KBEGraph {
    dag: KBEDAG,
    E: StagedVec<Equation>,
    R: StagedVec<Rule>,
}

/*
    insert a term into the KBE graph
*/
fn insert_term(t: &Term, kbe: &mut KBEDAG) -> Id {
    match t {
        Term::Variable(var) => {
            panic!("Cannot insert variable into KBE graph: {:?}", var);
        }
        Term::Function(f, ts) => {
            // embed all children, then create a new node (keep track of parent)
            let mut children = vec![];
            for t_prime in ts {
                // Recursively insert and canonicalize child Ids so interning uses canonical reps
                let child = insert_term(t_prime, kbe);
                let child = resolve_id(kbe, child);
                children.push(child);
            }
            // Ensure children vector itself is fully canonicalized (with respect to other nodes)
            let children = children.into_iter().map(|c| resolve_id(kbe, c)).collect();
            let node = ENode {
                label: *f,
                children,
            };
            if let Some(id) = kbe.C.get_by_right(&node) {
                return *id;
            }
            let id = kbe.id_count;
            kbe.id_count += 1;
            kbe.C.insert_no_overwrite(id, node).unwrap();
            return id;
        }
    }
}

fn extract_term(kbe: &KBEDAG, id: Id) -> Term {
    let node = kbe.C.get_by_left(&resolve_id(kbe, id)).unwrap();
    let mut children = vec![];
    for child in node.children.iter() {
        let child_term = extract_term(kbe, *child);
        children.push(child_term);
    }
    Term::Function(node.label, children)
}

fn fingerprint(t: &Term) -> u64 {
    use std::hash::{Hash, Hasher};
    use std::collections::hash_map::DefaultHasher;
    fn walk(term: &Term, hasher: &mut DefaultHasher) {
        match term {
            Term::Variable(x) => {
                // Distinguish node type and incorporate variable identity
                0u8.hash(hasher);
                x.hash(hasher);
            }
            Term::Function(f, ts) => {
                1u8.hash(hasher);
                f.hash(hasher);
                ts.len().hash(hasher);
                for child in ts.iter() {
                    walk(child, hasher);
                }
            }
        }
    }
    let mut hasher = DefaultHasher::new();
    walk(t, &mut hasher);
    hasher.finish()
}

fn match_rule_var(kbe: &KBEDAG, left: &Term, node_id: Id) -> bool {
    match_rule_var_subst(kbe, left, node_id, &mut vec![])
}

fn match_rule_var_subst(
    kbe: &KBEDAG,
    left: &Term,
    node_id: Id,
    subst: &mut Vec<(VarSym, Id)>,
) -> bool {
    // we know node is grounded
    // left might contain vars => if so, accociate them with the term at node if not in substset
    // if in substset, check if the term at node matches the substitution

    // instead of term at enode, we can use the enode directly
    // we know enodes are hashed => comparison on enode becomes identity check
    // TODO: operate on enode id
    let node_id = resolve_id(kbe, node_id);
    match left {
        Term::Variable(x) => {
            // println!(" DBG: Unify {:?} with {:?}", x, node_id);
            // if let Some((_, subst_id)) = subst.iter().find(|(var, _)| *var == *x) {
            if let Some((_, subst_id)) = subst.iter().find(|(var, _)| var == x) {
                // in subst, check if node matches
                *subst_id == node_id
            } else {
                // not in subst, add it
                subst.push((x.clone(), node_id));
                true
            }
        }
        Term::Function(f, ts) => {
            let node = kbe.C.get_by_left(&node_id).unwrap();
            *f == node.label
            // let node = kbe.C.get_by_left(&resolve_id(kbe, node_id)).unwrap();
            // f == &node.label
                && ts.len() == node.children.len()
                && ts
                    .iter()
                    .zip(node.children.iter())
                    .all(|(t, id)| match_rule_var_subst(kbe, t, *id, subst))
        }
    }
}

fn subst_node(kbe: &KBEDAG, ss: &Vec<(VarSym, Id)>, t: &Term) -> Term {
    // We might need the original term => keep it and only read it
    match t {
        Term::Variable(xi) => {
            if let Some((_, id)) = ss.iter().find(|(var, _)| var == xi) {
                // if we have a substitution for this variable, return the term at that id
                extract_term(kbe, *id)
            } else {
                t.clone() // no substitution, return original term
                // Term::Variable(xi)
            }
        }
        Term::Function(f, ts) => {
            let new_ts = ts.into_iter().map(|t| subst_node(kbe, ss, t)).collect();
            Term::Function(f.clone(), new_ts)
        }
    }
}

fn apply_rules_var<F>(
    lpo: &F,
    kbe: &mut KBEDAG,
    rules: &Vec<&Rule>,  // grounded rules
    // rules: &RuleSet,  // grounded rules
    both_sides: bool, // check reversed side for ground equations to add to rule set
) -> RuleSet
where
    F: Fn(&Term, &Term) -> bool,
{
    let mut applied = vec![];

    let mut rules : Vec<(&Term, &Term)> = if both_sides {
        rules
            .iter()
            .flat_map(|(l, r)| {
                vec![
                    (l, r), // add original rule
                    (r, l), // add reversed rule
                ]
            })
            .collect::<>()
    } else {
        rules
            .iter()
            .map(|(l, r)| (l, r))
            .collect::<>()
    };

    // Deterministic rule processing order
    rules.sort_by(|(l1, r1), (l2, r2)| {
        let k1 = (fingerprint(l1), fingerprint(r1));
        let k2 = (fingerprint(l2), fingerprint(r2));
        k1.cmp(&k2)
    });

    for (l, r) in rules.iter() {
        // Deterministic iteration over node ids
        let mut ids: Vec<Id> = kbe.C.left_values().cloned().collect();
        ids.sort();

        let mut rewrites = vec![];
        #[cfg(debug_assertions)]
        { println!("DBG2: Apply rules {:?} -> {:?}", strterm(l), strterm(r)); stdout().flush().unwrap(); }

        // TODO: we can not invent variables

        for id in ids {
            let id = resolve_id(kbe, id);
            // #[cfg(debug_assertions)] { println!("DBG2: Check Id {:?}", id); stdout().flush().unwrap(); }

            let mut subst = vec![];
            if match_rule_var_subst(kbe, l, id, &mut subst) {
                #[cfg(debug_assertions)]
                println!(
                    "DBG: Match rule {:?} -> {:?} on node {} ({})",
                    strterm(l),
                    strterm(r),
                    id,
                    strterm(&extract_term(kbe, id))
                );


                #[cfg(debug_assertions)] { println!("DBG2: Subst l"); stdout().flush().unwrap(); }
                // TODO: l_inst could be extract
                let l_inst = subst_node(kbe, &subst, l);
                // TODO: the extract and embed is unecessary and expensive!
                #[cfg(debug_assertions)] { println!("DBG2: Subst r"); stdout().flush().unwrap(); }
                let r_inst = subst_node(kbe, &subst, r);
                #[cfg(debug_assertions)] { println!("DBG2: Substed: {:?} -> {:?}", strterm(&l_inst), strterm(&r_inst)); stdout().flush().unwrap(); }

                debug_assert!(extract_term(kbe, id) == l_inst);

                // if lpo(&r_inst, &l_inst) {
                //     applied.push((r_inst, l_inst));
                // } else {
                //     rewrites.push((id, r_inst.clone()));
                //     applied.push((l_inst, r_inst));
                // }
                // TODO: lpo is bottleneck
                if lpo(&l_inst, &r_inst) {
            #[cfg(debug_assertions)] { println!("Before Clone"); stdout().flush().unwrap(); }
                    rewrites.push((id, l_inst, r_inst));
                    // applied.push((l_inst, r_inst));
                }else {
                    applied.push((r_inst, l_inst));
                }
            #[cfg(debug_assertions)] { println!("DBG2: After If"); stdout().flush().unwrap(); }
            }
        }

        // To avoid overlapping rewrites:
        let mut already_replaced = HashSet::default();
        // Deterministic application order for rewrites
        rewrites.sort_by(|(id1, l1, r1), (id2, l2, r2)| {
            id1.cmp(id2)
                .then_with(|| fingerprint(l1).cmp(&fingerprint(l2)))
                .then_with(|| fingerprint(r1).cmp(&fingerprint(r2)))
        });
        for (id, l,r) in rewrites {
            #[cfg(debug_assertions)]
            println!(
                "DBG: Replace node {} with new term {} (previously {})",
                id,
                strterm(&r),
                strterm(&extract_term(kbe, id))
            );

            // TODO: subterm might be replaced => might not be smaller anymore            
            // debug_assert!(lpo(&extract_term(kbe, id), &r));
            if already_replaced.contains(&id) {
                #[cfg(debug_assertions)]
                println!("DBG: Node {} already replaced, skipping", id);
                continue; // skip if already replaced in this batch
            }
            if !kbe.C.contains_left(&id) {
                continue; // skip if already removed by a previous rewrite
            }
            // TODO: r_id might already exist => do not first create but only construct term
            let r_id = insert_term(&r, kbe);
            kbe.C.remove_by_left(&id);
            debug_assert!(
                !kbe.S.contains_key(&id),
                "Node with id {} already replaced",
                id
            );
            kbe.S.insert(id, r_id);
            already_replaced.insert(id);
            applied.push((l, r));
        }
    }
    return applied;
}

fn simplify_dag_var<F>(lpo: &F, kbe: &mut KBEGraph) -> RuleSet
where
    F: Fn(&Term, &Term) -> bool,
{
    let mut new_rules = vec![];

    // TODO: rule application never result in new rules (always subsumed)
    #[cfg(debug_assertions)]
    println!("Apply R-rules");
    // for R we know the grounded instances
    // => no need to add
    // debug_assert!(&kbe.R.staged.is_empty());
    apply_rules_var(
        lpo,
        &mut kbe.dag,
        // &kbe.R.iter_all().collect::<Vec<_>>(),
        // &kbe.R.current,
        &kbe.R.current.iter().chain(
            kbe.R.staged.iter()
        ).collect::<Vec<_>>(),
        // &kbe.R
        //     .iter()
        //     .map(|(l, r)| (l.clone(), r.clone()))
        //     .collect::<Vec<_>>(),
        false,
    );
    // #[cfg(debug_assertions)]
    // println!("Apply R-rules inverse");
    // new_rules.extend(apply_rules_var(
    //     lpo,
    //     kbe,
    //     &kbe.R
    //         .iter()
    //         .map(|(l, r)| (r.clone(), l.clone()))
    //         .collect::<Vec<_>>(),
    //     false,
    // ));
    #[cfg(debug_assertions)]
    println!("Apply E-rules");
    // debug_assert!(&kbe.E.staged.is_empty());
    new_rules.extend(apply_rules_var(
        lpo,
        &mut kbe.dag,
        // &kbe.E.iter_all().collect::<Vec<_>>(),
        // &kbe.E.current,
        &kbe.E.current.iter().chain(
            kbe.E.staged.iter()
        ).collect::<Vec<_>>(),
        // &kbe.E
            // .iter()
            // .map(|(l, r)| (l.clone(), r.clone()))
            // .collect::<Vec<_>>(),
        true,
    ));

    // recanonicalize the dag
    canonicalize_dag(&mut kbe.dag);


    return new_rules;
    // Deduplicate newly generated equations and filter out ones already present in E or R
    // let mut dedup: RuleSet = vec![];
    // for eq in new_rules.into_iter() {
    //     let is_dup = dedup.iter().any(|e| sameeq(e, &eq))
    //         || kbe.E.iter_all().any(|e| sameeq(e, &eq))
    //         || kbe.R.iter_all().any(|r| sameeq(r, &eq));
    //     if !is_dup { dedup.push(eq); }
    // }
    // return dedup;
}

fn resolve_id(kbe: &KBEDAG, id: Id) -> Id {
    let mut id = id;
    while let Some(real_id) = kbe.S.get(&id) {
        id = *real_id;
    }
    id
}

fn canonicalize_dag(kbe: &mut KBEDAG) {
    // Repeatedly normalize children via resolve_id and merge duplicates until fixpoint
    loop {
        let mut changed = false;
        // Collect a stable snapshot to allow mutation during iteration
        let mut entries: Vec<(Id, ENode)> = kbe
            .C
            .iter()
            .map(|(id, node)| (*id, node.clone()))
            .collect();
        // Process in deterministic id order
        entries.sort_by_key(|(id, _)| *id);

        for (id, node) in entries.into_iter() {
            // Skip if id was redirected since snapshot
            if !kbe.C.contains_left(&id) {
                continue;
            }

            let resolved_children: Vec<Id> = node
                .children
                .iter()
                .map(|c| resolve_id(kbe, *c))
                .collect();

            if resolved_children != node.children {
                let new_node = ENode {
                    label: node.label,
                    children: resolved_children,
                };

                // If an identical canonical node already exists, redirect to the smaller id deterministically
                let redirect_to = kbe.C.get_by_right(&new_node).cloned();
                if let Some(existing_id) = redirect_to {
                    if existing_id != id {
                        // kbe.C.remove_by_left(&id);
                        // // Ensure we are not overwriting an existing mapping
                        // debug_assert!(kbe.S.get(&id).is_none());
                        // kbe.S.insert(id, existing_id);
                        let survivor = existing_id.min(id);
                        let victim = existing_id.max(id);
                        if kbe.C.contains_left(&victim) {
                            kbe.C.remove_by_left(&victim);
                        }
                        if victim != survivor {
                            debug_assert!(kbe.S.get(&victim).is_none());
                            kbe.S.insert(victim, survivor);
                        }
                        changed = true;
                        continue;
                    }
                }

                // Otherwise, update the node in place with canonical children
                kbe.C.remove_by_left(&id);
                kbe.C.insert_no_overwrite(id, new_node).unwrap();
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }
}

fn cleanup_dag(kbe: &mut KBEDAG, root: Id) {
    // Compute set of nodes reachable from the (resolved) root via resolved children
    let mut reachable: HashSet<Id> = HashSet::default();
    let mut stack: Vec<Id> = vec![resolve_id(kbe, root)];

    while let Some(id) = stack.pop() {
        if reachable.contains(&id) {
            continue;
        }
        if let Some(node) = kbe.C.get_by_left(&id) {
            reachable.insert(id);
            for child in node.children.iter() {
                stack.push(resolve_id(kbe, *child));
            }
        }
    }

    // Collect ids to remove (not reachable)
    let to_remove: Vec<Id> = kbe
        .C
        .left_values()
        .cloned()
        .filter(|id| !reachable.contains(id))
        .collect();

    // Remove unreachable nodes
    for id in to_remove.into_iter() {
        kbe.C.remove_by_left(&id);
    }

    // Prune stale substitutions: keep only mappings whose old id is still reachable
    // let stale_subs: Vec<Id> = kbe
    //     .S
    //     .keys()
    //     .cloned()
    //     .filter(|old_id| !reachable.contains(old_id))
    //     .collect();
    // for old_id in stale_subs.into_iter() {
    //     kbe.S.remove(&old_id);
    // }
}

#[derive(Default)]
struct SymbolCount {
    arity: usize,
    count: usize,
}

fn count_symbols(t: &Term, map: &mut HashMap<GlobalSymbol, SymbolCount>) {
    match t {
        Term::Variable(_) => {}
        Term::Function(f, ts) => {
            map.entry(*f).or_insert(SymbolCount { arity: ts.len(), count: 0 }).count += 1;
            for t_prime in ts {
                count_symbols(t_prime, map);
            }
        }
    }
}

fn term_contains(t: &Term, subterm: &Term) -> bool {
    if let Some(_) = collate(subterm, t) {
        return true;
    }
    match t {
        Term::Function(_, ts) => ts.iter().any(|t_prime| term_contains(t_prime, subterm)),
        _ => false,
    }
}

fn read_equations(path: &str) -> EquationSet {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|line| line.trim())
        .filter(|line| !line.is_empty() && !line.starts_with("//") && !line.starts_with("#"))
        .map(|line| parseeq(line))
        .collect()
}

#[derive(Parser)]
#[command(name = "kbo_rust")]
#[command(about = "KBO (Knuth-Bendix Ordering) implementation in Rust")]
struct Args {
    /// Rule file path
    #[arg(short, long, value_name = "RULEFILE")]
    rules: Option<String>,

    /// Term file path
    #[arg(short, long, value_name = "TERMFILE")]
    term: Option<String>,

    /// Number of iterations
    #[arg(short, long, default_value = "30")]
    iterations: usize,

    /// Positional arguments for backward compatibility
    #[arg(value_name = "POSITIONAL")]
    positional: Vec<String>,
}

fn cp_weight(w: &Weight, l: &Term, r: &Term, age: usize) -> usize {
    let l_size = term_weight(&w, &l);
    let r_size = term_weight(&w, &r);
    let size = if l_size > r_size { 4*l_size + r_size } else { l_size + 4*r_size };
    // TODO: dag weight
    size + age
}



// You can configure any percentile between 0 and 100
#[cfg_attr(feature = "hotpath", hotpath::main(percentiles = [50,99]))]
fn main() {
    let mut R: Vec<(Rule, usize)> = vec![]; // oriented rules (&age)
    let mut E: Vec<(Equation, usize)> = vec![]; // unorientable equations (&age)
    let mut Q: PriorityQueue<((Term, Term), usize), _> = PriorityQueue::new(); // critical pair (&age)
    let mut J: Vec<Equation> = vec![]; // stays empty for now

    let mut eqs = vec![];


    let start_time = std::time::Instant::now();
    let args = Args::parse();

    // Determine rule file path
    let rule_path = if let Some(path) = args.rules {
        path
    } else if !args.positional.is_empty() {
        args.positional[0].clone()
    } else {
        eprintln!(
            "Error: No rule file provided. Use --rules/-r or provide as first positional argument."
        );
        std::process::exit(1);
    };

    // Determine term file/path
    let term_arg = if let Some(term) = args.term {
        term
    } else if args.positional.len() > 1 {
        args.positional[1].clone()
    } else {
        eprintln!(
            "Error: No term provided. Use --term/-t or provide as second positional argument."
        );
        std::process::exit(1);
    };

    // Load equations from rule file
    let mut conj_term_override: Option<Term> = None;
    if rule_path.ends_with(".p") {
        let cnfs = p_parser::parse_p_file(&rule_path);
        // Convert axioms to equations; conjectures become the input term Eq(Expr1,Expr2)
        let mut conj_terms: Vec<Term> = Vec::new();
        let mut ax_count = 0usize;
        let mut cj_count = 0usize;
        for c in cnfs.into_iter() {
            match c.kind {
                p_parser::CnfKind::Axiom => { eqs.push(c.equation); ax_count += 1; }
                p_parser::CnfKind::Conjecture => {
                    let (l, r) = c.equation;
                    let eq_fun = symbol_table::GlobalSymbol::from("Eq");
                    let conj = Term::Function(eq_fun, vec![l, r]);
                    conj_terms.push(conj);
                    cj_count += 1;
                }
            }
        }
        println!("Loaded from .p: {} axioms, {} conjectures", ax_count, cj_count);
        // Add Eq(x,x) = True
        let eq_fun = symbol_table::GlobalSymbol::from("Eq");
        let true_fun = symbol_table::GlobalSymbol::from("True");
        let x = Term::Variable(VarSym(symbol_table::GlobalSymbol::from("X"), 0));
        let eq_xx = Term::Function(eq_fun, vec![x.clone(), x.clone()]);
        let rule_eq = (eq_xx, Term::Function(true_fun, vec![]));
        eqs.push(rule_eq);
        // Use first conjecture as input term if present
        conj_term_override = conj_terms.into_iter().next();
    } else {
        eqs = read_equations(&rule_path);
    }

    // Parse term (override from conjecture if provided by .p file)
    let t = if let Some(ct) = conj_term_override { ct } else {
        if std::path::Path::new(&term_arg).is_file() {
            parseterm(&std::fs::read_to_string(&term_arg).unwrap())
        } else {
            parseterm(&term_arg)
        }
    };

    // compute precedence by occurence count often => higher
    let mut symbol_counts = HashMap::default();
    count_symbols(&t, &mut symbol_counts);
    // set each to zero
    for (_, count) in symbol_counts.iter_mut() {
        // *count = 0; // reset counts
        count.count = 0;
    }
    for eq in eqs.iter() {
        count_symbols(&eq.0, &mut symbol_counts);
        count_symbols(&eq.1, &mut symbol_counts);
    }
    // Deterministic precedence: sort by (count desc, arity desc, symbol name asc)
    let mut sorted_symbols: Vec<_> = symbol_counts.into_iter().collect();
    // sorted_symbols.sort_by_key(|(_, count)| (count.count as i64) + 100*(count.arity as i64)); // sort by count descending
    // sorted_symbols.sort_by_key(|(_, count)| (count.arity, count.count));
    sorted_symbols.sort_by_key(|(s, count)| (count.arity, count.count, s.to_string()));
    // sorted_symbols.reverse();
    #[cfg(debug_assertions)]
    println!("Symbol counts:");
    #[cfg(debug_assertions)]
    for (symbol, count) in sorted_symbols.iter() {
        println!("  {}: {} ({})", symbol, count.count, count.arity);
    }
    // let sorted_symbols = vec![
    //     "Zero",
    //     "MinusOne",
    //     "A",
    //     "Mul",
    //     "Pow",
    //     "Div",
    // ].into_iter().map(|s| (s.to_string(), 0)).collect::<Vec<_>>();

    // create precedence from sorted symbols
    let mut pre: Precedence = vec![];
    for (i, (symbol, _)) in sorted_symbols.iter().enumerate() {
        pre.push((symbol.clone(), i as i32));
    }

    // pre.sort_by_key(|(_, count)| *count as i64);
    #[cfg(debug_assertions)]
    println!("Final precedence:");
    #[cfg(debug_assertions)]
    for (symbol, count) in pre.iter() {
        println!("  {}: {}", symbol, count);
    }

    // Step 0 (define precedence)
    // let lpo = |t: &Term, t_prime: &Term| lpo_gt(&pre, t, t_prime);
    // every symbol weight 1
    let mut w = vec![];
    // variable weight
    w.push(("?".into(), 0));
    for (symbol, _) in pre.iter() {
        w.push((symbol.clone(), 1));
    }
    // for (symbol, count) in pre.iter() {
    //     weight.push((symbol.clone(), (1+count) as usize));
    // }
    // let order = |t: &Term, t_prime: &Term| kbo_gt(&pre, &w, t, t_prime);
    let order = |t: &Term, t_prime: &Term| lpo_gt(&pre, t, t_prime);


    eqs.iter().for_each(|eq| {
        Q.push(((eq.0.clone(), eq.1.clone()), 0), cp_weight(&w, &eq.0, &eq.1, 0));
    });
    debug_assert!(R.is_empty());
    debug_assert!(E.is_empty());



    for i in 0..args.iterations {
        println!();
        println!();
        println!("Iteration {}", i);

        let (((t1, t2), age), _) = Q.pop().unwrap();





        println!("Intermediate State:");
        println!("Queue size: {}", Q.len());
        println!("Rules:");
        printrules_ref(&R.iter().map(|(r, _)| r).collect::<Vec<_>>());
        println!("Equations:");
        printeqs_ref(&E.iter().map(|(e, _)| e).collect::<Vec<_>>());

        println!("Original:");
        println!("{}", strterm(&t));
        println!("Result:");
        let t_prime = linorm_ref(&R.iter().map(|(r, _)| r).collect::<Vec<_>>(), &t);
        let t_prime_str = strterm(&t_prime);
        println!("{}", t_prime_str);
    }



// cargo run --bin main_kbc -- math_converted9.rule math_term3_eq3.txt -i 10



}
