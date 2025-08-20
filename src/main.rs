mod kbo;
mod term_rewrite;
mod types;
mod util;

use bimap::BiMap;
use clap::Parser;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::stdout;
use std::io::Write;

use crate::kbo::*;
use crate::term_rewrite::*;
use crate::types::*;

fn knuth_steps<F>(verbose: bool, lpo: &F, state: &(RuleSet, EquationSet)) -> (RuleSet, EquationSet)
where
    F: Fn(&Term, &Term) -> bool,
{
    // Orient, Compose, collapse => if orientable and new rule used
    // simplify, remove trivial => always

    let copy = state.clone();
    if let Ok(oriented) = orient_equation(lpo, copy) {
        let composed = compose(oriented);
        let collapsed = collapse(composed);
        let added = add_rule(collapsed);
        let simplified = simplify(added);
        let removed = remove_trivial(verbose, simplified);
        removed
    } else {
        let copy = state.clone();
        let simplified = simplify(copy);
        let removed = remove_trivial(verbose, simplified);
        removed
    }
}

fn knuth_loop<F>(verbose: bool, lpo: &F, state: (RuleSet, EquationSet)) -> (RuleSet, EquationSet)
where
    F: Fn(&Term, &Term) -> bool,
{
    let mut changed = true;
    let mut new_state = state;
    while changed {
        changed = false;
        let new_state_prime = knuth_steps(verbose, lpo, &new_state);
        if new_state != new_state_prime {
            changed = true;
            new_state = new_state_prime;
        }
    }
    new_state
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ENode {
    label: String, // TODO: globalize in table for efficiency
    children: Vec<Id>,
}

type Id = usize;

#[allow(non_snake_case)]
struct KBEGraph {
    C: BiMap<Id, ENode>, // can be done as Vec<ENode> with id as index, and an additional C_inv
    id_count: usize,
    E: EquationSet,
    R: RuleSet,
    // replacement_set: old_id -> new_id (old_id no longer exists in C)
    S: HashMap<Id, Id>, // used to keep track of replacements
}

/*
    insert a term into the KBE graph
*/
fn insert_term(t: &Term, kbe: &mut KBEGraph) -> Id {
    match t {
        Term::Variable(var) => {
            panic!("Cannot insert variable into KBE graph: {:?}", var);
        }
        Term::Function(f, ts) => {
            // TODO: normalize here or is input always normalized?
            // embed all children, then create a new node (keep track of parent)
            let mut children = vec![];
            for t_prime in ts {
                let child = insert_term(t_prime, kbe);
                children.push(child);
            }
            let node = ENode {
                label: f.clone(),
                children,
            };
            if let Some(id) = kbe.C.get_by_right(&node) {
                return id.clone();
            }
            let id = kbe.id_count;
            kbe.id_count += 1;
            kbe.C.insert_no_overwrite(id, node).unwrap();
            return id;
        }
    }
}

fn extract_term(kbe: &KBEGraph, id: Id) -> Term {
    let node = kbe.C.get_by_left(&resolve_id(kbe, id)).unwrap();
    let mut children = vec![];
    for child in node.children.iter() {
        let child_term = extract_term(kbe, *child);
        children.push(child_term);
    }
    Term::Function(node.label.clone(), children)
}

fn match_rule_var(kbe: &KBEGraph, left: &Term, node_id: Id) -> bool {
    match_rule_var_subst(kbe, left, node_id, &mut vec![])
}

fn match_rule_var_subst(
    kbe: &KBEGraph,
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
    match left {
        Term::Variable(x) => {
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
            let node = kbe.C.get_by_left(&resolve_id(kbe, node_id)).unwrap();
            f == &node.label
                && ts.len() == node.children.len()
                && ts
                    .iter()
                    .zip(node.children.iter())
                    .all(|(t, id)| match_rule_var_subst(kbe, t, *id, subst))
        }
    }
}

pub fn subst_node(kbe: &KBEGraph, ss: &Vec<(VarSym, Id)>, t: &Term) -> Term {
    match t {
        Term::Variable(xi) => {
            if let Some((_, id)) = ss.iter().find(|(var, _)| var == xi) {
                // if we have a substitution for this variable, return the term at that id
                extract_term(kbe, *id)
            } else {
                t.clone() // no substitution, return original term
            }
        }
        Term::Function(f, ts) => {
            let new_ts = ts.iter().map(|t| subst_node(kbe, ss, t)).collect();
            Term::Function(f.clone(), new_ts)
        }
    }
}

fn apply_rules_var<F>(
    lpo: &F,
    kbe: &mut KBEGraph,
    rules: &RuleSet,  // grounded rules
    both_sides: bool, // check reversed side for ground equations to add to rule set
) -> RuleSet
where
    F: Fn(&Term, &Term) -> bool,
{
    let mut applied = vec![];

    let rules = if both_sides {
        rules
            .iter()
            .flat_map(|(l, r)| {
                vec![
                    (l.clone(), r.clone()), // add original rule
                    (r.clone(), l.clone()), // add reversed rule
                ]
            })
            .collect::<RuleSet>()
    } else {
        rules
            .iter()
            .map(|(l, r)| (l.clone(), r.clone()))
            .collect::<RuleSet>()
    };

    for (l, r) in rules.iter() {
        // for id in kbe.C.left_values() {
        let ids = kbe.C.iter().map(|(id, _)| (id.clone()));

        let mut rewrites = vec![];
        #[cfg(debug_assertions)]
        { println!("DBG2: Apply rules {:?} -> {:?}", strterm(l), strterm(r)); stdout().flush().unwrap(); }

        // TODO: we can not invent variables

        for id in ids {
            #[cfg(debug_assertions)] { println!("DBG2: Check Id {:?}", id); stdout().flush().unwrap(); }

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
                    rewrites.push((id, r_inst.clone()));
                    applied.push((l_inst, r_inst));
                }else {
                    applied.push((r_inst, l_inst));
                }
            #[cfg(debug_assertions)] { println!("DBG2: After If"); stdout().flush().unwrap(); }
            }
        }

        // To avoid overlapping rewrites:
        let mut already_replaced = std::collections::HashSet::new();
        for (id, r) in rewrites {
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
        }
    }
    return applied;
}

fn simplify_dag_var<F>(lpo: &F, kbe: &mut KBEGraph) -> RuleSet
where
    F: Fn(&Term, &Term) -> bool,
{
    let mut new_rules = vec![];

    #[cfg(debug_assertions)]
    println!("Apply R-rules");
    new_rules.extend(apply_rules_var(
        lpo,
        kbe,
        &kbe.R
            .iter()
            .map(|(l, r)| (l.clone(), r.clone()))
            .collect::<Vec<_>>(),
        false,
    ));
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
        kbe,
        &kbe.E
            .iter()
            .map(|(l, r)| (l.clone(), r.clone()))
            .collect::<Vec<_>>(),
        true,
    ));
    return new_rules;
}

fn resolve_id(kbe: &KBEGraph, id: Id) -> Id {
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

fn count_symbols(t: &Term, map: &mut HashMap<String, SymbolCount>) {
    match t {
        Term::Variable(_) => {}
        Term::Function(f, ts) => {
            map.entry(f.clone()).or_insert(SymbolCount { arity: ts.len(), count: 0 }).count += 1;
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
    let args = Args::parse();

    let mut kbe = KBEGraph {
        C: BiMap::new(),
        id_count: 0,
        E: vec![],
        R: vec![],
        S: HashMap::new(),
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
    kbe.E = read_equations(&rule_path);

    // Parse term
    let t = if std::path::Path::new(&term_arg).is_file() {
        parseterm(&std::fs::read_to_string(&term_arg).unwrap())
    } else {
        parseterm(&term_arg)
    };

    let t_id = insert_term(&t, &mut kbe);
    let mut ids = kbe.C.left_values().cloned().collect::<Vec<_>>();
    ids.sort();
    #[cfg(debug_assertions)]
    for id in ids.iter() {
        let node = kbe.C.get_by_left(id).unwrap();
        println!(
            "  {}: {} ({}({}))",
            id,
            strterm(&extract_term(&kbe, *id)),
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
    for (symbol, count) in symbol_counts.iter_mut() {
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
    sorted_symbols.sort_by_key(|(_, count)| ((count.count as i64) + 100*(count.arity as i64))); // sort by count descending
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

    // Step 3 (loop)
    for i in 0..args.iterations {
        println!();
        println!();
        println!("Iteration {}", i);
        #[cfg(debug_assertions)]
        println!("DAG:");
        let mut ids = kbe.C.left_values().cloned().collect::<Vec<_>>();
        ids.sort();
        #[cfg(debug_assertions)]
        for id in ids.iter() {
            let node = kbe.C.get_by_left(id).unwrap();
            println!(
                "  {}: {} ({}({}))",
                id,
                strterm(&extract_term(&kbe, *id)),
                node.label,
                node.children
                    .iter()
                    .map(|c| c.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }

        // Step 3.1 (E-Graph: Apply rules on graph)
        // TODO: without 3.2 this would not resolve as equations are oriented
        // we would just eagerly rewrite the graph? (adding rules to R help? or that we keep the subexpressions?)
        // let ground_instances = ground_instances(&kbe);
        let mut instances: HashSet<Term> = HashSet::new();
        let mut visited: HashMap<ENode, Term> = HashMap::new();
        // assert that all rules in R are oriented according to the lpo
        #[cfg(debug_assertions)]
        for rule in kbe.R.iter() {
            let (l, r) = rule;
            if !lpo(l, r) {
                panic!("Rule not oriented: {:?} > {:?}", strterm(l), strterm(r));
            }
        }

        // TODO: also at rewrite order
        // add all instances to E, knuth bendix (orient, simpl)
        // or only if left/right in C

        // is from E already onriented/grounded is oriented

        #[cfg(debug_assertions)]
        println!("Simplify DAG.");
        let new_rules = simplify_dag_var(&lpo, &mut kbe); 
        #[cfg(debug_assertions)]
        println!("New rules:");
        #[cfg(debug_assertions)]
        printrules(&new_rules);
        // kbe.E.extend(new_rules);
        kbe.R.extend(new_rules);

        // Step 3.2 (KBO: Add critical pairs)
        // TODO: keep previous critical pairs instead of complete recomputation
        let mut cps = vec![];

        {
            // let rules = kbe.R.clone();
            let mut rules = kbe.R.clone();
            // R + E in both direction
            rules.extend(kbe.E.iter().map(|(l, r)| (l.clone(), r.clone())));
            rules.extend(kbe.E.iter().map(|(l, r)| (r.clone(), l.clone())));
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
                #[cfg(debug_assertions)]
                println!(
                    "DBG: Critical pair: {} -> {} with {} -> {}",
                    strterm(&rule1.0),
                    strterm(&rule1.1),
                    strterm(&rule2.0),
                    strterm(&rule2.1)
                );
                let cp = critical_pair(rule1, rule2);
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
                        let l_prime = linorm(&kbe.R, &l);
                        let r_prime = linorm(&kbe.R, &r);
                        (l_prime, r_prime)
                    })
                    .filter(|(l, r)| {
                        // only keep if not trivial
                        l != r && !kbe.E.contains(&(l.clone(), r.clone()))
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
                cps.extend(simpl_cp);
            }
        }

        }
        #[cfg(debug_assertions)]
        println!("Computed {} critical pairs", cps.len());
        // TODO: only add some critical pairs (ematch or grounded (how many from R are subsumed))
        // kbe.E.extend(cps);
        // simp via R, match on C

        // for each node in C, search if a cps applies, count how often
        let mut counted_cps = cps
            .iter()
            .map(|cp| {
                let (l, r) = cp;
                let mut count = 0;
                for (id, _) in kbe.C.iter() {
                    // TODO: need to match ground instance
                    // TODO: we do not want to match on variable only right side
                    let is_var_l = match l {
                        Term::Variable(_) => true, // do not match on variable
                        Term::Function(_, _) => false,
                    };
                    let is_var_r = match r {
                        Term::Variable(_) => true, // do not match on variable
                        Term::Function(_, _) => false,
                    };
                    let match_left = match_rule_var(&kbe, &l, *id);
                    let match_right = match_rule_var(&kbe, &r, *id);
                    if (!is_var_l && match_left) || (!is_var_r && match_right) {
                        count += 1;
                    }
                }

                let mut rule_count = 0;
                for (l_rule, r_rule) in kbe.R.iter() {
                    if term_contains(&l_rule, l) {
                        rule_count += 1;
                    }
                    if term_contains(&r_rule, l) {
                        rule_count += 1;
                    }
                    if term_contains(&l_rule, r) {
                        rule_count += 1;
                    }
                    if term_contains(&r_rule, r) {
                        rule_count += 1;
                    }
                }

                let size = (strterm(&l).len() + strterm(&r).len()) as i32;

                (cp, count, rule_count, size)
            })
            // TODO: filter does not work
            // e.g. group axioms with Mul(A, Mul(Inv(A), B)) -> B
            // the first critical pair would be (One, Mul(Inv(x), Mul(x,z))) but that does not occur in the graph
            // .filter(|(_, count)| *count > 0) // only keep those with count > 0
            .collect::<Vec<_>>();
        // sort by count descending
        // counted_cps.sort_by_key(|(_, count)| -count.clone());
        // counted_cps.sort_by_key(|(_, count, rule_count, size)| (-count.clone(), -rule_count.clone(), size.clone()));
        // counted_cps.sort_by_key(|(_, count, rule_count, size)| size.clone());
        // counted_cps.sort_by_key(|(_, count, rule_count, size)| -count.clone());

        counted_cps.sort_by_key(|(_, count, rule_count, size)| {
            (size.clone(), -rule_count.clone(), -count.clone())
        });

        // counted_cps.sort_by_key(|(_, count, rule_count)| (-count.clone()+ -rule_count.clone()));
        // take top 5 to extend E
        let top_cps = counted_cps
            .into_iter()
            .take(5)
            .map(|(cp, _, _, _)| cp.clone())
            .collect::<Vec<_>>();
        // let top_cps = counted_cps.into_iter().map(|(cp, _, _, _)| cp.clone()).collect::<Vec<_>>();
        #[cfg(debug_assertions)]
        println!("Top 5 critical pairs:");
        #[cfg(debug_assertions)]
        for (l, r) in top_cps.iter() {
            println!("  {} = {}", strterm(l), strterm(r));
        }
        // TODO: not clone
        kbe.E.extend(top_cps);

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
        println!("{}", strterm(&t_prime));
        // exit(0);
        let t_extract = extract_term(&kbe, t_id);
        println!("Extracted term:");
        println!("{}", strterm(&t_extract));
    }

    // match using R and E (ground instances)
    // add matched ones to R
}
