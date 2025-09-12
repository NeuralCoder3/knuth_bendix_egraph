mod kbo;
mod term_rewrite;
mod types;
mod util;
mod p_parser;

use bimap::BiMap;
use clap::Parser;
// use std::collections::HashMap;
// use std::collections::HashSet;
use hashbrown::HashSet;
use hashbrown::HashMap;
use std::io::stdout;
use std::io::Write;
use std::time::Duration;
use std::time::Instant;
use symbol_table::GlobalSymbol;

use crate::kbo::*;
use crate::term_rewrite::*;
use crate::types::*;

fn knuth_steps<F>(verbose: bool, lpo: &F, state: (RuleSet, EquationSet)) -> (bool,(RuleSet, EquationSet))
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

fn knuth_loop<F>(verbose: bool, lpo: &F, state: (RuleSet, EquationSet)) -> (RuleSet, EquationSet)
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
    E: EquationSet,
    R: RuleSet,
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
                let child = insert_term(t_prime, kbe);
                children.push(child);
            }
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
            if let Some((_, subst_id)) = subst.iter().find(|(var, _)| *var == *x) {
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
    rules: &RuleSet,  // grounded rules
    both_sides: bool, // check reversed side for ground equations to add to rule set
) -> RuleSet
where
    F: Fn(&Term, &Term) -> bool,
{
    let mut applied = vec![];

    let rules : Vec<(&Term, &Term)> = if both_sides {
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

    for (l, r) in rules.iter() {
        // for id in kbe.C.left_values() {
        let ids = kbe.C.iter().map(|(id, _)| *id);

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
        let mut already_replaced = HashSet::new();
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
    apply_rules_var(
        lpo,
        &mut kbe.dag,
        &kbe.R,
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
    new_rules.extend(apply_rules_var(
        lpo,
        &mut kbe.dag,
        &kbe.E,
        // &kbe.E
            // .iter()
            // .map(|(l, r)| (l.clone(), r.clone()))
            // .collect::<Vec<_>>(),
        true,
    ));
    return new_rules;
}

fn resolve_id(kbe: &KBEDAG, id: Id) -> Id {
    let mut id = id;
    while let Some(real_id) = kbe.S.get(&id) {
        id = *real_id;
    }
    id
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

fn main() {
    let start_time = std::time::Instant::now();
    let args = Args::parse();

    let mut kbe = KBEGraph {
        dag: KBEDAG { 
            C: BiMap::new(),
            id_count: 0,
            S: HashMap::new(),
        },
        E: vec![],
        R: vec![],
    };

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
        let mut eqs: EquationSet = Vec::new();
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
        kbe.E = eqs;
    } else {
        kbe.E = read_equations(&rule_path);
    }

    // Parse term (override from conjecture if provided by .p file)
    let t = if let Some(ct) = conj_term_override { ct } else {
        if std::path::Path::new(&term_arg).is_file() {
            parseterm(&std::fs::read_to_string(&term_arg).unwrap())
        } else {
            parseterm(&term_arg)
        }
    };

    let t_id = insert_term(&t, &mut kbe.dag);
    let mut ids = kbe.dag.C.left_values().cloned().collect::<Vec<_>>();
    ids.sort();
    #[cfg(debug_assertions)]
    for id in ids.iter() {
        let node = kbe.dag.C.get_by_left(id).unwrap();
        println!(
            "  {}: {} ({}({}))",
            id,
            strterm(&extract_term(&kbe.dag, *id)),
            node.label,
            node.children
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }

    // compute precedence by occurence count often => higher
    let mut symbol_counts = HashMap::new();
    count_symbols(&t, &mut symbol_counts);
    // set each to zero
    for (_, count) in symbol_counts.iter_mut() {
        // *count = 0; // reset counts
        count.count = 0;
    }
    for eqs in kbe.E.iter() {
        count_symbols(&eqs.0, &mut symbol_counts);
        count_symbols(&eqs.1, &mut symbol_counts);
    }
    for rule in kbe.R.iter() {
        count_symbols(&rule.0, &mut symbol_counts);
        count_symbols(&rule.1, &mut symbol_counts);
    }
    // sort by count descending
    let mut sorted_symbols: Vec<_> = symbol_counts.into_iter().collect();
    sorted_symbols.sort_by_key(|(_, count)| (count.count as i64) + 100*(count.arity as i64)); // sort by count descending
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
    let lpo = |t: &Term, t_prime: &Term| lpo_gt(&pre, t, t_prime);

    #[cfg(debug_assertions)]
    {
    println!("Rules:");
    printrules(&kbe.R);
    println!("Equations:");
    printeqs(&kbe.E);
    println!("KBC Step");
    }

    kbe.R = vec![];
    let state = knuth_loop(true, &lpo, (kbe.R, kbe.E));
    kbe.R = state.0;
    kbe.E = state.1;


    


    let t_prime = linorm(&kbe.R, &t);
    println!("Rules:");
    printrules(&kbe.R);
    println!("Equations:");
    printeqs(&kbe.E);
    println!("Original:");
    println!("{}", strterm(&t));
    println!("Result:");
    println!("{}", strterm(&t_prime));

    let mut current_result = None;
    let mut achieved_time = None;
    let mut step31_total = std::time::Duration::from_secs(0);
    let mut step32_total = std::time::Duration::from_secs(0);
    // Global critical pair cache across iterations, keyed by owned rule content
    let mut critical_pair_cache: HashMap<((Term, Term), (Term, Term)), Vec<(Term, Term)>> = HashMap::new();

    // Step 3 (loop)
    for i in 0..args.iterations {
        println!();
        println!();
        println!("Iteration {}", i);
        #[cfg(debug_assertions)]
        println!("DAG:");
        let mut ids = kbe.dag.C.left_values().cloned().collect::<Vec<_>>();
        ids.sort();
        #[cfg(debug_assertions)]
        for id in ids.iter() {
            let node = kbe.dag.C.get_by_left(id).unwrap();
            println!(
                "  {}: {} ({}({}))",
                id,
                strterm(&extract_term(&kbe.dag, *id)),
                node.label,
                node.children
                    .iter()
                    .map(|c| resolve_id(&kbe.dag, *c).to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }

        // Step 3.1 (E-Graph: Apply rules on graph)
        // Note: alone this is not egraph as we only keep smaller terms
        // the larger terms are represented by R but we do not act on the left sides of R in 3.1
        // assert that all rules in R are oriented according to the lpo
        #[cfg(debug_assertions)]
        for rule in kbe.R.iter() {
            let (l, r) = rule;
            if !lpo(l, r) {
                panic!("Rule not oriented: {:?} > {:?}", strterm(l), strterm(r));
            }
        }

        // we simplify the DAG with R and E
        // all (grounded) instances from R are already known and need to not be added
        // instances from E are oriented, replaced in the DAG and recorded

        #[cfg(debug_assertions)]
        println!("Simplify DAG.");
        let step31_start = std::time::Instant::now();
        let new_rules = simplify_dag_var(&lpo, &mut kbe); 
        #[cfg(debug_assertions)]
        println!("New rules:");
        #[cfg(debug_assertions)]
        printrules(&new_rules);
        // new rules should always be ground and are already oriented
        // however, rules are not considered in mutual simplification => need first be added to E
        // 3.2 will take care of the simplification
        kbe.E.extend(new_rules);
        step31_total += step31_start.elapsed();

        // Step 3.2 (KBO: Add critical pairs)
        // TODO: keep previous critical pairs instead of complete recomputation
        let step32_start = std::time::Instant::now();
        let mut cps = vec![];

        {
            // let rules = kbe.R.clone();
            let mut rules = kbe.R.iter().map(|(l, r)| (l, r)).collect::<Vec<_>>();
            // R + E in both direction
            rules.extend(kbe.E.iter().map(|(l, r)| (l, r)));
            rules.extend(kbe.E.iter().map(|(l, r)| (r, l)));
            // Use the global cache across iterations
            // Per-iteration normalization cache used by linorm_cached
            let mut norm_cache: HashMap<Term, Term> = HashMap::new();
            let mut normalize = |t: &Term| -> Term { linorm_cached(&kbe.R, t, &mut norm_cache) };
        // let rules = kbe.R.iter().flat_map(|(l, r)| {
        //     vec![
        //         (l.clone(), r.clone()), // add original rule
        //         (r.clone(), l.clone()), // add reversed rule
        //     ]
        // }).collect::<Vec<_>>();

        for (i, rule1) in rules.iter().enumerate() {
            for (j, rule2) in rules.iter().enumerate() {
                if i > j {
                    continue; // only consider pairs once
                }
                // Use owned Term pairs as cache key so mutations to rule sets don't affect identity
                let key = (
                    (rule1.0.clone(), rule1.1.clone()),
                    (rule2.0.clone(), rule2.1.clone())
                );
                if let Some(cached_raw_cp) = critical_pair_cache.get(&key) {
                    // cps.extend(cached_raw_cp.clone());
                    // Re-simplify cached raw CPs using the current R and filter against current R/E
                    let simpl_cp = cached_raw_cp
                        .iter()
                        .cloned()
                        // .map(|(l, r)| {
                        //     let l_prime = normalize(&l);
                        //     let r_prime = normalize(&r);
                        //     (l_prime, r_prime)
                        // })
                        .filter(|(l, r)| {
                            l != r
                            && !kbe.E.iter().any(|eq| sameeq(eq, &(l.clone(), r.clone())))
                            && !kbe.R.iter().any(|rule| sameeq(rule, &(l.clone(), r.clone())))
                        })
                        .collect::<Vec<_>>();
                    cps.extend(simpl_cp);
                    continue;
                }

                #[cfg(debug_assertions)]
                println!(
                    "DBG: Critical pair: {} -> {} with {} -> {}",
                    strterm(&rule1.0),
                    strterm(&rule1.1),
                    strterm(&rule2.0),
                    strterm(&rule2.1)
                );
                let cp = critical_pair_ref((rule1.0, rule1.1), (rule2.0, rule2.1));
                // let cp = critical_pair(&key.0, &key.1);
                #[cfg(debug_assertions)]
                for (c_l, c_r) in cp.iter() {
                    println!(
                        "DBG:   OrgCritical pair: {} = {}",
                        strterm(c_l),
                        strterm(c_r)
                    );
                }

                // simplify using R
                let simpl_cp = cp
                    .into_iter()
                    .map(|(l, r)| {
                        let l_prime = normalize(&l);
                        let r_prime = normalize(&r);

                        // normalize variables

                        (l_prime, r_prime)
                    })
                    .filter(|(l, r)| {
                        // only keep if not trivial
                        l != r
                        && !kbe.E.iter().any(|eq| sameeq_ref((&eq.0,&eq.1), (l, r)))
                        && !kbe.R.iter().any(|rule| sameeq_ref((&rule.0,&rule.1), (l, r)))
                        // && !kbe.E.contains(&(l.clone(), r.clone())) 
                        // && !kbe.E.contains(&(r.clone(), l.clone())) 
                        // && !kbe.R.iter().any(|(l_r, r_r)| (l == l_r && r == r_r) || (l == r_r && r == l_r))
                    })
                    .collect::<Vec<_>>();
                if simpl_cp.is_empty() {
                    continue;
                }
                #[cfg(debug_assertions)]
                for (simpl_l, simpl_r) in simpl_cp.iter() {
                    println!(
                        "DBG:  Simplified critical pair: {} = {}",
                        strterm(simpl_l),
                        strterm(simpl_r)
                    );
                }
                critical_pair_cache.insert(key, simpl_cp.clone());
                cps.extend(simpl_cp);
            }
        }

        }
        #[cfg(debug_assertions)]
        println!("Computed {} critical pairs", cps.len());

        // for each node in C, search if a cps applies, count how often
        let mut counted_cps = cps
            .iter()
            // .cloned()

            // dedup for testing, TODO: should not be necessary
            .collect::<HashSet<_>>()
            .into_iter()
            .map(|cp| {
                let (l, r) = cp;
                let mut count = 0;
                // we do not want to match on variable only right side
                let is_var_l = match l {
                    Term::Variable(_) => true, // do not match on variable
                    Term::Function(_, _) => false,
                };
                let is_var_r = match r {
                    Term::Variable(_) => true, // do not match on variable
                    Term::Function(_, _) => false,
                };
                if !is_var_l {
                    for id in kbe.dag.C.left_values() {
                        if match_rule_var(&kbe.dag, &l, *id) {
                            count += 1;
                        }
                    }
                }
                if !is_var_r {
                    for id in kbe.dag.C.left_values() {
                        if match_rule_var(&kbe.dag, &r, *id) {
                            count += 1;
                        }
                    }
                }
                // for (id, _) in kbe.C.iter() {
                //     let match_left = match_rule_var(&kbe, &l, *id);
                //     let match_right = match_rule_var(&kbe, &r, *id);
                //     if (!is_var_l && match_left) || (!is_var_r && match_right) {
                //         count += 1;
                //     }
                // }

                let mut rule_count = 0;
                for (l_rule, r_rule) in kbe.R.iter() {
                    if term_contains(&l_rule, &l) {
                        rule_count += 1;
                    }
                    if term_contains(&r_rule, &l) {
                        rule_count += 1;
                    }
                    if term_contains(&l_rule, &r) {
                        rule_count += 1;
                    }
                    if term_contains(&r_rule, &r) {
                        rule_count += 1;
                    }
                }

                let size = (strterm(&l).len() + strterm(&r).len()) as i32;

                ((l,r), (count, rule_count, size))
            })
            .collect::<Vec<_>>();

        counted_cps.sort_by_key(|(_, (count, rule_count, size))| {
            (size.clone(), -rule_count.clone(), -count.clone())
            // size.clone()
        });

        // take top 5 to extend E
        let top_cps = counted_cps
            .into_iter()
            .take(5)
            .map(|(cp, _)| cp)
            // .map(|((l,r), _)| (l.clone(), r.clone()))
            .collect::<Vec<_>>();
        
        #[cfg(debug_assertions)]
        println!("Top 5 critical pairs:");
        #[cfg(debug_assertions)]
        for (l, r) in top_cps.iter() {
            println!("  {} = {}", strterm(l), strterm(r));
        }
        kbe.E.extend(top_cps.into_iter().map(|(l, r)| (l.clone(), r.clone())));
        step32_total += step32_start.elapsed();

        #[cfg(debug_assertions)]
        println!("Rules before KBC:");
        #[cfg(debug_assertions)]
        printrules(&kbe.R);


        // kbo faster because only considers relevant critical pairs
        let state = knuth_loop(true, &lpo, (kbe.R, kbe.E));
        kbe.R = state.0;
        kbe.E = state.1;

        println!("Intermediate State:");
        println!("Rules:");
        printrules(&kbe.R);
        println!("Equations:");
        printeqs(&kbe.E);

        println!("Original:");
        println!("{}", strterm(&t));
        println!("Result:");
        let t_prime = linorm(&kbe.R, &t);
        let t_prime_str = strterm(&t_prime);
        println!("{}", t_prime_str);

        let t_extract = extract_term(&kbe.dag, t_id);
        println!("Extracted term:");
        println!("{}", strterm(&t_extract));

        if current_result.is_none() || current_result.as_ref().unwrap() != &t_prime_str {
            current_result = Some(t_prime_str);
            achieved_time = Some(start_time.elapsed());
        }
        println!(
            "Time elapsed: {:.2?} ({:.2?} | {:.2?})",
            start_time.elapsed(),
            step31_total,
            step32_total
        );
        if let Some(achieved_time) = achieved_time {
            println!("Achieved after: {:.2?}", achieved_time);
        }
    }

    // match using R and E (ground instances)
    // add matched ones to R
}
