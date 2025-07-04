mod kbo;
mod term_rewrite;
mod types;
mod util;

use bimap::BiMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io;
use std::process::exit;
use std::time::Instant;
use term_rewrite::parseeqs;

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
        // println!("Oriented:");
        // printrule(&oriented.0);
        let composed = compose(oriented);
        // println!("Compose");
        let collapsed = collapse(composed);
        // println!("Collapse");
        let added = add_rule(collapsed);
        // println!("Add");
        let simplified = simplify(added);
        // println!("Simplify");
        // let simplified = added;
        let removed = remove_trivial(verbose, simplified);
        // println!("Remove trivial");
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
        // println!("Knuth loop");
        changed = false;
        // let (rules, eqs) = new_state;
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

// // some id:usize outside, with map (C) usize -> Node  (bidirectional)
// // term -> id: construct analogous nod, look up in inverse C

// #[derive(Debug, Clone)]
// struct RawNode {
//     label: String,
//     children: Vec<Node>,
//     // TODO: handle multiple parents
// }
// // type Node = Rc<RefCell<RawNode>>; // RefCell needed to set parent children pointer
// type Node = RawNode;

// fn Node(label: String, children: Vec<Node>) -> Node {
//     let node = RawNode {
//         label,
//         children: children.clone(),
//     };
//     node
// }

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
            // TODO: panic? term should be grounded
            panic!("Cannot insert variable into KBE graph: {:?}", var);
            // variable becomes a leaf (recursive calls will handle parents)
            // let node = ENode {
            //     label: var.0.clone(),
            //     children: vec![],
            // };
            // #[allow(non_snake_case)]
            // let C = &mut kbe.C;
            // if let Some(id) = C.get_by_right(&node) {
            //     return id.clone();
            // }
            // let id = kbe.id_count;
            // kbe.id_count += 1;
            // C.insert_no_overwrite(id, node).unwrap();
            // return id;
        }
        Term::Function(f, ts) => {
            // TODO: normalize here or is input always normalized?
            // embed all children, then create a new node (keep track of parent)
            let mut children = vec![];
            for t_prime in ts {
                let child = insert_term(t_prime, kbe);
                children.push(child);
            }
            // DEBUG: all children exist
            // for child in children.iter() {
            //     if !kbe.C.contains_left(child) {
            //         panic!("Child id {} not found in C", child);
            //     }
            // }
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

/*
    with C, recursively extracts all ground terms from the graph
*/
fn ground_instances(
    visited: &mut HashMap<ENode, Term>,
    instances: &mut HashSet<Term>,
    node: &ENode,
    kbe: &KBEGraph,
) -> Term {
    if visited.contains_key(node) {
        return visited[node].clone();
    }
    let mut children = vec![];
    for child in node.children.iter() {
        let child_node = kbe.C.get_by_left(&resolve_id(kbe, *child)).unwrap();
        let child_node = ground_instances(visited, instances, child_node, kbe);
        children.push(child_node.clone());
    }
    let term = Term::Function(node.label.clone(), children);
    visited.insert(node.clone(), term.clone());
    instances.insert(term.clone());
    term
}

/*
    rewrites the kbe graph with a grounded rule
*/
// fn rewriteRule(rule: &Rule) {}

fn instantiations(vars: &Vec<VarSym>, t: &HashSet<Term>) -> Vec<SubstitutionSet> {
    if vars.is_empty() {
        return vec![vec![]];
    }
    let mut result = vec![];
    let var = &vars[0];
    for t_prime in t.iter() {
        let mut insts = instantiations(&vars[1..].to_vec(), t);
        for inst in insts.iter_mut() {
            inst.push((var.clone(), t_prime.clone()));
        }
        result.extend(insts);
    }
    result
}

fn match_rule(kbe: &KBEGraph, left: &Term, node: &ENode) -> bool {
    match left {
        Term::Variable(_) => panic!("Rule should be grounded"),
        Term::Function(f, ts) => {
            f == &node.label
                && ts.len() == node.children.len()
                && ts.iter().zip(node.children.iter()).all(|(t, id)| {
                    let child = kbe.C.get_by_left(&resolve_id(kbe, *id)).unwrap();
                    match_rule(kbe, t, child)
                })
        }
    }
}


fn match_rule_var(kbe: &KBEGraph, left: &Term, node_id: Id) -> bool {
    match_rule_var_subst(kbe, left, node_id, &mut vec![])
}


fn match_rule_var_subst(kbe: &KBEGraph, left: &Term, node_id: Id, subst: &mut Vec<(VarSym, Id)>) -> bool {
    // we know node is grounded
    // left might contain vars => if so, accociate them with the term at node if not in substset
    // if in substset, check if the term at node matches the substitution

    // instead of term at enode, we can use the enode directly
    // we know enodes are hashed => comparison on enode becomes identity check
    // TODO: operate on enode id
    match left {
        Term::Variable(x) => 
            if let Some((_, subst_id)) = subst.iter().find(|(var, _)| var == x) {
                // in subst, check if node matches
                *subst_id == node_id
            } else {
                // not in subst, add it
                subst.push((x.clone(), node_id));
                true
            },
        Term::Function(f, ts) => {
            let node = kbe.C.get_by_left(&resolve_id(kbe, node_id)).unwrap();
            f == &node.label
                && ts.len() == node.children.len()
                && ts.iter().zip(node.children.iter()).all(|(t, id)| {
                    match_rule_var_subst(kbe, t, *id, subst)
                })
        }
    }
}

// fn match_rule(
//     kbe: &mut KBEGraph,
//     rules: &RuleSet, // grounded rules
//     node: &ENode
// ) -> Option<RuleSet> {
//     let applicable = rules.iter()
//         .filter(|(l, _)| {
//             match l {
//                 Term::Variable(_) => panic!("Rule should be grounded"),
//                 Term::Function(f, ts) => f == &node.label &&
//                     ts.len() == node.children.len() &&
//                     ts.iter().zip(node.children.iter()).all(|(t, id)| {
//                         let child = kbe.C.get_by_left(id).unwrap();
//                         apply_rules_here(kbe, rules, node)
//                     })
//             }
//         });
//     false
// }

fn apply_rules(
    kbe: &mut KBEGraph,
    rules: &RuleSet,  // grounded rules
    both_sides: bool, // check reversed side for ground equations to add to rule set
) -> RuleSet {
    let mut applied = vec![];
    for (id, node) in kbe.C.iter() {
        let applicable = rules.iter().filter(|(l, _)| match_rule(kbe, l, node));
        applied.extend(
            // TODO: double map not necessary
            applicable.map(|rule| {
                // TODO: clone not necessary
                (id.clone(), rule)
            }),
        );
    }

    // TODO: assert no two rules match simultaneously?
    // well that can happen => handle it


    // replace id by (embedded) right term
    for (i, rule) in applied.iter() {
        // we insert the term resulting in id r_id
        // then we need to replace the old node
        // remove new r_id node, i node and write to i
        println!("  Replace node {} with new term {} (previously {} = {})", i, strterm(&rule.1), strterm(&rule.0), strterm(&extract_term(kbe, *i)));
        let (_l, r) = rule;
        // TODO: r_id might already exist => do not first create but only construct term
        let r_id = insert_term(r, kbe);
        kbe.C.remove_by_left(i);
        assert!(!kbe.S.contains_key(i), "Node with id {} already replaced", i);
        kbe.S.insert(*i, r_id); // keep track of replacement

        // replace all children of i with r_id
        // for node_id in kbe.C.left_values().cloned().collect::<Vec<_>>() {
        //     let node = kbe.C.get_by_left(&node_id).unwrap();
        //     if node.children.contains(i) {
        //         let new_children: Vec<Id> = node.children.iter().map(|child_id| {
        //             if child_id == i {
        //                 r_id // replace i with r_id
        //             } else {
        //                 *child_id // keep other children
        //             }
        //         }).collect();
        //         let new_node = ENode {
        //             label: node.label.clone(),
        //             children: new_children,
        //         };
        //         // replace node in C with new_node
        //         kbe.C.insert(node_id, new_node);
        //     }
        // }

        // let node = kbe.C.get_by_left(&r_id).unwrap().clone(); // TODO: clone necessary as owner is bound to kbe
        //                                                       // unassociate r_id
        // kbe.C.remove_by_left(&r_id);
        // kbe.C.remove_by_left(i);
        // let result = kbe.C.insert_no_overwrite(*i,node.clone());
        // if result.is_err() {
        //     panic!("Node with id {} already exists in C", i);
        // }
        // println!("  Inserted new node with id {} replacing {}", r_id, i);
        // assert!(kbe.C.contains_left(i), "Node with id {} not found in C", i);
        // println!("  Id {} now contains term: {}", i, strterm(&extract_term(kbe, *i)));
        // assert!(kbe.C.contains_left(&i.clone()), "Node with id {} not found in C", i);
        // assert!(!kbe.C.contains_left(&r_id), "Node with id {} still exists in C", r_id);
    }

    // // validate the egraph
    // for (id, node) in kbe.C.iter() {
    //     // check if all children are in C
    //     for child_id in node.children.iter() {
    //         if !kbe.C.contains_left(child_id) {
    //             panic!("Child id {} not found in C for node {}", child_id, id);
    //         }
    //     }
    // }

    // both sides => check if right sides matches then add rules to applied
    if both_sides {
        for (id, node) in kbe.C.iter() {
            let applicable = rules.iter().filter(|(_, r)| match_rule(kbe, r, node));
            applied.extend(applicable.map(|rule| {
                // TODO: clone not necessary
                (id.clone(), rule)
            }))
        }
        // deduplicate
        applied.sort_by_key(|(id, _)| id.clone());
        applied.dedup_by_key(|(id, _)| id.clone());
    }

    // let old_nodes = kbe.C.right_values().cloned().collect::<Vec<_>>();
    // for node in old_nodes.iter() {
    //     let applicable = rules.iter()
    //         .filter(|(left, _)| {
    //             match_rule(kbe, left, node)
    //         });
    //     for rule in applicable {
    //         let (l, r) = rule;
    //         let r_id = insert_term(r, kbe);
    //     }
    // }
    return applied
        .into_iter()
        .map(|(_, rule)| {
            rule.clone() // TODO: clone not necessary
        })
        .collect::<Vec<_>>();
}

fn simplify_dag<F>(lpo: &F, kbe: &mut KBEGraph, ground_instances: &HashSet<Term>) -> RuleSet
where
    F: Fn(&Term, &Term) -> bool,
{
    let mut new_rules = vec![];

    let rules = kbe
        .R
        .iter()
        .map(|(l, r)| (l.clone(), r.clone()))
        .flat_map(|(l, r)| instantiate_pair(lpo, &l, &r, ground_instances, true))
        .collect::<Vec<_>>();
    new_rules.extend(apply_rules(kbe, &rules, false));
    let eq_rules = kbe
        .E
        .iter()
        .map(|(l, r)| (l.clone(), r.clone()))
        .flat_map(|(l, r)| instantiate_pair(lpo, &l, &r, ground_instances, false))
        .collect::<Vec<_>>();
    new_rules.extend(apply_rules(kbe, &eq_rules, true));

    // let lr_eqs = kbe
    //     .E
    //     .iter()
    //     .map(|(l, r)| (l.clone(), r.clone()))
    //     .collect::<Vec<_>>();
    // let rl_eqs = kbe
    //     .E
    //     .iter()
    //     .map(|(l, r)| (r.clone(), l.clone()))
    //     .collect::<Vec<_>>();
    // let rules = kbe
    //     .R
    //     .iter()
    //     .chain(lr_eqs.iter())
    //     .chain(rl_eqs.iter())
    //     .collect::<Vec<_>>();
    // // let mut i = 0;
    // for rule in rules.iter() {
    //     // println!("Rule {}: {:?}", i, rule);
    //     // i += 1;
    //     let (l, r) = rule;
    //     let vars = vars(l)
    //         .iter()
    //         .chain(vars(r).iter()) // e.g. in equation fst(x,y) = x
    //         .cloned()
    //         .collect::<HashSet<_>>()
    //         .into_iter()
    //         .collect::<Vec<_>>();
    //     // println!("  Vars: {:?}", vars);
    //     let insts = instantiations(&vars, ground_instances);
    //     // println!("  Instantiations: {:?}", insts);
    //     for inst in insts.iter() {
    //         // println!("    Instantiation: {:?}", inst);
    //         let l_inst = subst(inst, l);
    //         let r_inst = subst(inst, r);
    //         // println!("      Instantiated: {:?} = {:?}", l_inst, r_inst);
    //         let rule_inst = (l_inst, r_inst);
    //         new_rules.push(rule_inst.clone());
    //         // let changed = simplify_dag_with_rule(dag, &rule_inst);
    //         // if changed {
    //         //     output.push(rule_inst);
    //         // }
    //     }
    // }
    // return new_rules
    // only add the applicable ones
    // return vec![];
    // return new_rules.iter().flat_map(|rule| {
    //     apply_rules(kbe, rules)
    // }).collect::<Vec<_>>();

    // return apply_rules(kbe, &new_rules);
    return new_rules;
}

fn instantiate_pair<F>(
    lpo: &F,
    l: &Term,
    r: &Term,
    ground_instances: &HashSet<Term>,
    already_oriented: bool, // as a safety check for our rules (remove orient here for efficiency)
) -> Vec<(Term, Term)>
where
    F: Fn(&Term, &Term) -> bool,
{
    // if already_oriented {
    //     assert!(lpo(&l, &r));
    // }
    let mut new_rules = vec![];
    let vars = vars(l)
        .iter()
        .chain(vars(r).iter()) // e.g. in equation fst(x,y) = x
        .cloned()
        .collect::<HashSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    // println!("  Vars: {:?}", vars);
    let insts = instantiations(&vars, ground_instances);
    // println!("  Instantiations: {:?}", insts);
    for inst in insts.iter() {
        // println!("    Instantiation: {:?}", inst);
        let l_inst = subst(inst, l);
        let r_inst = subst(inst, r);
        // println!("      Instantiated: {:?} = {:?}", l_inst, r_inst);
        // new_rules.push((l_inst, r_inst));

        // (l,r) if lpo(l,r)

        if lpo(&l_inst, &r_inst) {
            new_rules.push((l_inst, r_inst));
        } else if lpo(&r_inst, &l_inst) {
            if already_oriented {
                assert!(lpo(&l, &r));
                panic!(
                    "Rule already oriented: {:?} > {:?} (but order should be ground_complete) (instance of rule {:?} = {:?})",
                    strterm(&l_inst), strterm(&r_inst), strterm(l), strterm(r)
                );
            }
            new_rules.push((r_inst, l_inst));
        } else {
            panic!(
                "Neither side is greater: {:?} = {:?} (but order should be ground_complete)",
                l_inst, r_inst
            );
        }
        // let changed = simplify_dag_with_rule(dag, &rule_inst);
        // if changed {
        //     output.push(rule_inst);
        // }
    }
    return new_rules;
}


pub fn subst_node(kbe: &KBEGraph, ss: &Vec<(VarSym,Id)>, t: &Term) -> Term {
    match t {
        Term::Variable(xi) => {
            if let Some((_, id)) = ss.iter().find(|(var, _)| var == xi) {
                // if we have a substitution for this variable, return the term at that id
                extract_term(kbe, *id)
            } else {
                t.clone() // no substitution, return original term
            }
            // if let Some(s) = find_substitution(xi, ss) {
            //     s.clone()
            // } else {
            //     t.clone()
            // }
        }
        Term::Function(f, ts) => {
            let new_ts = ts.iter().map(|t| subst_node(kbe,ss, t)).collect();
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
    // where applied, should rewrite, rule
    let mut applied = vec![];

    for (l,r) in kbe.R.iter() {
        for id in kbe.C.left_values() {
            let mut subst = vec![];
            if match_rule_var_subst(kbe, l, *id, &mut subst) {
                println!("DBG: Match rule {:?} -> {:?} on node {} ({})", strterm(l), strterm(r), id, strterm(&extract_term(kbe, *id)));
                // TODO: l_inst could be extract
                let l_inst = subst_node(kbe, &subst, l);
                // TODO: the extract and embed is unecessary and expensive!
                let r_inst = subst_node(kbe, &subst, r);
                println!("DBG:   Instantiated: {} -> {:?}", strterm(&l_inst), strterm(&r_inst));
                // check both_sides for efficiency -- otherwise we already know l_inst > r_inst
                if both_sides && lpo(&r_inst, &l_inst) {
                    println!("DBG:     Oriented in reverse (not rewrite)");
                    applied.push((id.clone(), false, (r_inst, l_inst)));
                }else {
                    applied.push((id.clone(), true, (l_inst, r_inst)));
                }
            }
            if both_sides {
                let mut subst = vec![];
                if match_rule_var_subst(kbe, r, *id, &mut subst) {
                    println!("DBG: Match rule {:?} -> {:?} on node {} ({})", strterm(r), strterm(l), id, strterm(&extract_term(kbe, *id)));
                    // TODO: l_inst could be extract
                    let l_inst = subst_node(kbe, &subst, l);
                    // TODO: the extract and embed is unecessary and expensive!
                    let r_inst = subst_node(kbe, &subst, r);
                    println!("DBG:   Instantiated: {} -> {:?}", strterm(&r_inst), strterm(&l_inst));
                    if lpo(&l_inst, &r_inst) {
                        println!("DBG:     Oriented in reverse (not rewrite)");
                        applied.push((id.clone(), false, (l_inst, r_inst)));
                    }else {
                        applied.push((id.clone(), true, (r_inst, l_inst)));
                    }
                }
            }
        }
    }

    for (i, should_rewrite, (_,r)) in applied.iter() {
        if !should_rewrite {
            continue;
        }
        // we insert the term resulting in id r_id
        // then we need to replace the old node
        // remove new r_id node, i node and write to i
        println!("DBG: Replace node {} with new term {} (previously {})", i, strterm(&r), strterm(&extract_term(kbe, *i)));
        // TODO: r_id might already exist => do not first create but only construct term
        let r_id = insert_term(&r, kbe);
        kbe.C.remove_by_left(i);
        assert!(!kbe.S.contains_key(i), "Node with id {} already replaced", i);
        kbe.S.insert(*i, r_id); // keep track of replacement
    }

    // both sides => check if right sides matches then add rules to applied
    // if both_sides {
    //     for (id, node) in kbe.C.iter() {
    //         // let applicable = rules.iter().filter(|(_, r)| match_rule_var(kbe, r, node));
    //         // applied.extend(applicable.map(|rule| {
    //         //     // TODO: clone not necessary
    //         //     (id.clone(), rule)
    //         // }))
    //         for (rule_l, rule_r) in rules.iter() {
    //             let mut subst = vec![];
    //             if match_rule_var_subst(kbe, rule_r, *id, &mut subst) {
    //                 println!("DBG: Rev-Match rule {:?} -> {:?} on node {} ({})", strterm(rule_l), strterm(rule_r), id, strterm(&extract_term(kbe, *id)));
    //                 let l_inst = subst_node(kbe, &subst, rule_l);
    //                 let r_inst = subst_node(kbe, &subst, rule_r);
    //                 println!("DBG:  Instantiated: {} -> {:?}", strterm(&l_inst), strterm(&r_inst));
    //                 applied.push((id.clone(), (l_inst, r_inst)));
    //             }
    //         }
    //     }
    //     // deduplicate
    //     applied.sort_by_key(|(id, _)| id.clone());
    //     applied.dedup_by_key(|(id, _)| id.clone());
    // }

    return applied
        .into_iter()
        .map(|(_, _, rule)| {
            rule.clone() // TODO: clone not necessary
        })
        .collect::<Vec<_>>();
}

fn simplify_dag_var<F>(lpo: &F, kbe: &mut KBEGraph) -> RuleSet
where
    F: Fn(&Term, &Term) -> bool,
{
    let mut new_rules = vec![];

    new_rules.extend(
        apply_rules_var(
            lpo,
            kbe, 
            &kbe.R.iter()
                .map(|(l, r)| (l.clone(), r.clone()))
                .collect::<Vec<_>>(),
            false
    ));
    new_rules.extend(
        apply_rules_var(
            lpo,
            kbe, 
            &kbe.E.iter()
                .map(|(l, r)| (l.clone(), r.clone()))
                .collect::<Vec<_>>(),
            true
    ));


    // let applied = vec![];

    // for (l,r) in kbe.R.iter() {
    //     for id in kbe.C.left_values() {
    //         let mut subst = vec![];
    //         if match_rule_var_subst(kbe, l, id, &mut subst) {
    //             println!("Match rule {:?} on node {}", strterm(l), id);
    //             // TODO: the extract and embed is unecessary and expensive!
    //             let r_inst = subst_node(kbe, &subst, r);
    //             println!("  Instantiated: {:?}", r_inst);
    //             applied.push((id, r_inst));
    //             // // // println!("  Substitution: {:?}", subst);
    //             // // let r_inst = subst(r, &subst);
    //             // // // println!("  Instantiated: {:?}", r_inst);
    //             // let r_id = insert_term(&r_inst, kbe);
    //             // // println!("  Inserted new term with id {}", r_id);
    //             // kbe.C.remove_by_left(&id);
    //             // assert!(!kbe.S.contains_key(&id), "Node with id {} already replaced", id);
    //             // kbe.S.insert(id, r_id); // keep track of replacement
    //         }
    //     }
    // }


    // for (i, r) in applied.iter() {
    //     // we insert the term resulting in id r_id
    //     // then we need to replace the old node
    //     // remove new r_id node, i node and write to i
    //     println!("  Replace node {} with new term {} (previously {})", i, strterm(&r), strterm(&extract_term(kbe, *i)));
    //     // TODO: r_id might already exist => do not first create but only construct term
    //     let r_id = insert_term(r, kbe);
    //     kbe.C.remove_by_left(i);
    //     assert!(!kbe.S.contains_key(i), "Node with id {} already replaced", i);
    //     kbe.S.insert(*i, r_id); // keep track of replacement
    // }
    // panic!("Not implemented yet");

    // let rules = kbe
    //     .R
    //     .iter()
    //     .map(|(l, r)| (l.clone(), r.clone()))
    //     .flat_map(|(l, r)| instantiate_pair(lpo, &l, &r, ground_instances, true))
    //     .collect::<Vec<_>>();
    // new_rules.extend(apply_rules(kbe, &rules, false));
    // let eq_rules = kbe
    //     .E
    //     .iter()
    //     .map(|(l, r)| (l.clone(), r.clone()))
    //     .flat_map(|(l, r)| instantiate_pair(lpo, &l, &r, ground_instances, false))
    //     .collect::<Vec<_>>();
    // new_rules.extend(apply_rules(kbe, &eq_rules, true));

    return new_rules;
}




// { I(M(x, y)) -> M(I(y), I(x))
//   M(x, M(I(x), z)) -> z
//   M(x, I(x)) -> E
//   I(I(x)) -> x
//   I(E) -> E
//   M(x, E) -> x
//   M(I(x), M(x, z)) -> z
//   M(M(x, y), z) -> M(x, M(y, z))
//   M(I(x), x) -> E
//   M(E, x) -> x }


fn resolve_id(kbe: &KBEGraph, id: Id) -> Id {
    let mut id = id;
    while let Some(real_id) = kbe.S.get(&id) {
        id = *real_id;
    }
    id
    // if let Some(real_id) = kbe.S.get(&id) {
    //     return *real_id;
    // }
    // id
}


// fn count_symbols(t: &Term) -> HashMap<String, usize> {
//     let mut counts = HashMap::new();
//     match t {
//         Term::Variable(var) => {
//             *counts.entry(var.0.clone()).or_insert(0) += 1;
//         }
//         Term::Function(f, ts) => {
//             *counts.entry(f.clone()).or_insert(0) += 1;
//             for t_prime in ts {
//                 let child_counts = count_symbols(t_prime);
//                 for (k, v) in child_counts.iter() {
//                     *counts.entry(k.clone()).or_insert(0) += v;
//                 }
//             }
//         }
//     }
//     counts
// }
fn count_symbols(t: &Term, map: &mut HashMap<String, usize>) {
    match t {
        Term::Variable(_) => {
        }
        Term::Function(f, ts) => {
            *map.entry(f.clone()).or_insert(0) += 1;
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
        Term::Function(_, ts) => {
            ts.iter().any(|t_prime| term_contains(t_prime, subterm))
        }
        _ => false,
    }
}


fn main() {
    let mut kbe = KBEGraph {
        C: BiMap::new(),
        id_count: 0,
        E: vec![],
        R: vec![],
        S: HashMap::new(),
    };

    // // Step 0 (define precedence)
    // let pre: Precedence = vec![
    //     (String::from("M"), 1),
    //     (String::from("E"), 2),
    //     (String::from("I"), 3),
    //     (String::from("A"), 0), // e.g. for test term
    //     (String::from("B"), 0), // e.g. for test term
    // ];
    // let lpo = |t: &Term, t_prime: &Term| lpo_gt(&pre, t, t_prime);

    // // Step 1 (build KBE graph)

    // // let t = parseterm("M(I(M(y,M(x, M(I(x), I(y))))),z)"); // -> z
    // // let t = parseterm("M(I(M(b,M(a, M(I(a), I(b))))),c)"); // -> c
    // // let t = parseterm("M(I(x), M(x, z))"); // -> z
    // let t = parseterm("M(I(A), M(A, B))"); // -> B
    // let t_id = insert_term(&t, &mut kbe);

    // // Step 2 (orient rules in initial KBO step)
    // kbe.E = parseeqs(vec!["M(M(x,y),z)=M(x,M(y,z))", "M(I(x),x)=E", "M(E,x)=x"]);
    // let t = parseterm("M(I(A), M(A, B))"); // -> B


    // Step 1 (build KBE graph)

    // Step 2 (orient rules in initial KBO step)
//     kbe.E = parseeqs(
//         vec![
// "f=App(App(B,f),I)", // eta-expansion
// "App(App(App(B,x),y),z)=App(x,App(y,z))", // reduce-B
// "App(App(App(R,x),y),z)=App(App(y,z),x)", // reduce-R
// "App(App(App(S,x),y),z)=App(App(x,z),App(y,z))", // reduce-S
// "App(I,x)=x", // reduce-I
// "App(App(K,x),y)=x", // reduce-K
// "App(App(App(C,x),y),z)=App(App(x,z),y)", // reduce-C
// "App(x,App(y,z))=App(App(App(B,x),y),z)", // reduce-B-inv
// "App(App(y,z),x)=App(App(App(R,x),y),z)", // reduce-R-inv
// "App(App(x,z),App(y,z))=App(App(App(S,x),y),z)", // reduce-S-inv
// "App(App(x,z),y)=App(App(App(C,x),y),z)", // reduce-C-inv
// "App(App(B,S),K)=B", // char-B-1
// "App(S,App(K,x))=App(B,x)", // char-B-2
// "App(C,C)=R", // char-R-1
// "App(App(B,B),App(C,I))=R", // char-R-2
// "App(B,App(App(C,I),x))=App(R,x)", // char-R-3
// "App(B,I)=I", // char-I-1
// "App(App(S,K),x)=I", // char-I-2
// "App(C,App(K,I))=K", // char-K-1
// "App(App(C,App(App(B,B),S)),K)=C", // char-C-1
// "App(App(B,App(S,x)),K)=App(C,x)", // char-C-2
// "App(App(C,App(App(B,B),S)),K)=C", // char-C-3
// "App(App(S,x),App(K,y))=App(App(C,x),y)", // char-C-4
// "B=App(App(B,S),K)", // char-B-1-inv
// "App(B,x)=App(S,App(K,x))", // char-B-2-inv
// "R=App(C,C)", // char-R-1-inv
// "R=App(App(B,B),App(C,I))", // char-R-2-inv
// "App(R,x)=App(B,App(App(C,I),x))", // char-R-3-inv
// "I=App(B,I)", // char-I-1-inv
// "K=App(C,App(K,I))", // char-K-1-inv
// "C=App(App(C,App(App(B,B),S)),K)", // char-C-1-inv
// "App(C,x)=App(App(B,App(S,x)),K)", // char-C-2-inv
// "C=App(App(C,App(App(B,B),S)),K)", // char-C-3-inv
// "App(App(C,x),y)=App(App(S,x),App(K,y))", // char-C-4-inv
// "App(App(B,App(App(B,x),y)),z)=App(App(B,x),App(App(B,y),z))", // assoc-B-1
// "App(App(B,x),App(App(B,y),z))=App(App(B,App(App(B,x),y)),z)", // assoc-B-2


// // "App(App(map,f),nil)=nil", // map-nil (commented out)
// // "App(App(map,f),App(App(cons,x),xs))=App(App(cons,App(f,x)),App(App(map,f),xs))", // map-cons (commented out)
// // "App(isnil,nil)=true", // isnil-nil (commented out)
// // "App(isnil,App(App(cons,x),xs))=false", // isnil-cons (commented out)
// // "App(App(Add,f),0)=f", // Add-neutral-1 (commented out)
// "App(App(Add,0),f)=f", // Add-neutral-2
// "App(App(R,0),Add)=I", // Add-neutral-3
// "App(App(Add,f),App(Neg,f))=0", // Add-inverse-1
// "App(App(Add,App(Neg,f)),f)=0", // Add-inverse-2
// "App(App(S,Add),Neg)=0", // Add-inverse-3
// "App(App(Add,App(App(Add,f),g)),h)=App(App(Add,f),App(App(Add,g),h))", // Add-comm-1
// "App(App(Add,f),App(App(Add,g),h))=App(App(Add,App(App(Add,f),g)),h)", // Add-comm-2
// "App(C,Add)=Add", // Add-comm-3
// "Add=App(C,Add)", // Add-comm-4
// "App(App(Add,App(App(Add,f),g)),h)=App(App(Add,f),App(App(Add,g),h))", // Add-assoc-1
// "App(App(Add,f),App(App(Add,g),h))=App(App(Add,App(App(Add,f),g)),h)", // Add-assoc-2
// "App(App(Add,App(App(mul,a),b)),App(App(mul,a),c))=App(App(mul,a),App(App(Add,b),c))", // distr-l-1
// "App(App(S,App(App(B,C),App(App(B,App(B,B)),App(App(B,App(B,Add)),mul)))),mul)=App(App(R,Add),App(App(B,B),App(App(B,B),mul)))", // distr-l-2
// "App(App(B,Neg),Neg)=I", // double-neg
//         ]
//     );
    
//     // \\ c b. (add (mul c b) (mul c (neg b)))
//     //  (app (app S (app (app B S) (app (app B (app B add)) mul))) (app (app R neg) (app (app B B) mul)))
//     let t = parseterm("App(App(S, App(App(B, S), App(App(B, App(B, Add)), Mul))), App(App(R, Neg), App(App(B, B), Mul)))"); // -> 0



    // https://homepage.divms.uiowa.edu/~astump/papers/stump_loechner06.pdf
    // https://cs.bc.edu/stumpaa/papers/thesis-wehrman.pdf
    kbe.E = parseeqs(
        vec![
            // Group (Figure 3-1/3-2, page 25)
            // "Mul(One, x) = One",
            // "Mul(Mul(x, y), z) = Mul(x, Mul(y, z))",
            // "Mul(Inv(x), x) = One",
            "M(E, x) = x",
            "M(M(x, y), z) = M(x, M(y, z))",
            "M(I(x), x) = E",

            // One Group Endomorphism (Figure 7-1/7-2, page 51)
            // "F(M(x, y)) = M(F(x), F(y))",

            // Two Commuting Endomorphisms (Figure 7-5/7-6, page 53)
            // "G(Mul(x, y)) = Mul(G(x), G(y))",
            // "Mul(F(x), G(y)) = Mul(G(y), F(x))",

            // Three Commuting Endomorphisms (https://github.com/iwehrman/Slothrop/blob/master/tests/cge3.tptp)
            // "H(Mul(x, y)) = Mul(H(x), H(y))",
            // "Mul(F(x), H(y)) = Mul(H(y), F(x))",
            // "Mul(G(x), H(y)) = Mul(H(y), G(x))",
        ]
    );
    // let t = parseterm("Mul(A, Mul(Inv(A), Mul(Mul(B, C), Mul(Inv(C), Inv(B)))))"); // -> One
    // let t = parseterm("M(A, M(I(A), M(M(B, C), M(I(C), I(B)))))"); // -> One
    // let t = parseterm("M(A, M(I(A), B))"); // -> One
    let t = parseterm("M(A, I(A))"); // -> One




    let t_id = insert_term(&t, &mut kbe);
        let mut ids = kbe.C.left_values().cloned().collect::<Vec<_>>();
        ids.sort();
        for id in ids.iter() {
            let node = kbe.C.get_by_left(id).unwrap();
            println!("  {}: {} ({}({}))", id, strterm(&extract_term(&kbe, *id)), node.label, node.children.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(", "));
        }
        // panic!();

    // compute precedence by occurence count often => higher
    let mut symbol_counts = HashMap::new();
    count_symbols(&t, &mut symbol_counts);
    // set each to zero
    for (symbol, count) in symbol_counts.iter_mut() {
        *count = 0; // reset counts
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
    sorted_symbols.sort_by_key(|(_, count)| (*count as i64)); // sort by count descending
    // sorted_symbols.reverse();
    // print out count
    println!("Symbol counts:");
    for (symbol, count) in sorted_symbols.iter() {
        println!("  {}: {}", symbol, count);
    }
    // create precedence from sorted symbols
    let mut pre: Precedence = vec![
    ];
    for (i, (symbol, _)) in sorted_symbols.iter().enumerate() {
        // println!("  Precedence: {:?}", precedence);
        pre.push((symbol.clone(), i as i32));
    }


    // let mut pre: Precedence = vec![
    //     (String::from("M"), 1),
    //     (String::from("E"), 2),
    //     (String::from("I"), 3),

    //     // for test term
    //     (String::from("A"), 0), 
    //     (String::from("B"), 0),
    //     (String::from("C"), 0),
    // ];

    pre.sort_by_key(|(_, count)| *count as i64);
    println!("Final precedence:");
    for (symbol, count) in pre.iter() {
        println!("  {}: {}", symbol, count);
    }

    // panic!();
    // Step 0 (define precedence)
    let lpo = |t: &Term, t_prime: &Term| lpo_gt(&pre, t, t_prime);


    // let pre: Precedence = vec![
    //     (String::from("I"), 3),
    //     (String::from("M"), 1),
    //     (String::from("E"), 2),
    //     (String::from("A"), 0), // e.g. for test term
    //     (String::from("B"), 0), // e.g. for test term
    // ];
    // let lpo = |t: &Term, t_prime: &Term| lpo_gt(&pre, t, t_prime);



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
    for i in 0..3 {
        println!();
        println!();
        println!("Iteration {}", i);
        println!("DAG:");
        let mut ids = kbe.C.left_values().cloned().collect::<Vec<_>>();
        ids.sort();
        for id in ids.iter() {
            let node = kbe.C.get_by_left(id).unwrap();
            println!("  {}: {} ({}({}))", id, strterm(&extract_term(&kbe, *id)), node.label, node.children.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(", "));
        }

        // Step 3.1 (E-Graph: Apply rules on graph)
        // TODO: without 3.2 this would not resolve as equations are oriented
        // we would just eagerly rewrite the graph? (adding rules to R help? or that we keep the subexpressions?)
        // let ground_instances = ground_instances(&kbe);
        let mut instances: HashSet<Term> = HashSet::new();
        let mut visited: HashMap<ENode, Term> = HashMap::new();
        // for (_, enode) in kbe.C.iter() {
        //     // b
        //     let _ = ground_instances(&mut visited, &mut instances, enode, &kbe);
        // }
        // println!("Number of ground instances: {}", instances.len());
        // for t in instances.iter() {
        //     println!("  {}", strterm(t));
        // }
        // assert that all rules in R are oriented according to the lpo
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

        
        println!("Simplify DAG.");
        // // rules + ->eq + <-eq
        // let new_rules = simplify_dag(&lpo, &mut kbe, &instances);
        let new_rules = simplify_dag_var(&lpo, &mut kbe);
        println!("New rules:");
        printrules(&new_rules);
        // kbe.R.extend(new_rules);
        kbe.E.extend(new_rules);

        // Step 3.2 (KBO: Add critical pairs)
        // TODO: keep previous critical pairs instead of complete recomputation
        let mut cps = vec![];
        for (i, rule1) in kbe.R.iter().enumerate() {
            for (j, rule2) in kbe.R.iter().enumerate() {
                if i > j {
                    continue; // only consider pairs once
                }
                println!("DBG: Critical pair: {} -> {} with {} -> {}", strterm(&rule1.0), strterm(&rule1.1), strterm(&rule2.0), strterm(&rule2.1));
                let cp = critical_pair(rule1, rule2);
                for (c_l, c_r) in cp.iter() {
                    println!("DBG:   OrgCritical pair: {} = {}", strterm(c_l), strterm(c_r));
                }
                // simplify using R
                let simpl_cp = 
                    cp.into_iter()
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
                // println!("DBG: Critical pair: {} -> {} with {} -> {}", strterm(&rule1.0), strterm(&rule1.1), strterm(&rule2.0), strterm(&rule2.1));
                for (simpl_l, simpl_r) in simpl_cp.iter() {
                    println!("DBG:  Simplified critical pair: {} = {}", strterm(simpl_l), strterm(simpl_r));
                }
                cps.extend(simpl_cp);
            }
        }
        println!("Computed {} critical pairs", cps.len());
        // TODO: only add some critical pairs (ematch or grounded (how many from R are subsumed))
        // kbe.E.extend(cps);
        // simp via R, match on C

        // for each node in C, search if a cps applies, count how often
        let mut counted_cps =
        cps.iter()
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
        counted_cps.sort_by_key(|(_, count, rule_count, size)| (-count.clone(), -rule_count.clone(), size.clone()));
        // counted_cps.sort_by_key(|(_, count, rule_count)| (-count.clone()+ -rule_count.clone()));
        // take top 5 to extend E
        let top_cps = counted_cps.into_iter().take(5).map(|(cp, _, _, _)| cp.clone()).collect::<Vec<_>>();
        // let top_cps = counted_cps.into_iter().map(|(cp, _)| cp.clone()).collect::<Vec<_>>();
        println!("Top 5 critical pairs:");
        for (l, r) in top_cps.iter() {
            println!("  {} = {}", strterm(l), strterm(r));
        }
        // TODO: not clone
        kbe.E.extend(
            top_cps
        );



        // counted_cps.iter().take(5).for_each(|(cp, _)| {
        //     let (l, r) = cp;
        //     kbe.E.push((l.clone(), r.clone()));
        // });
        // let top_cps = counted_cps.iter().take(5).map(|(cp, _)| cp.clone()).collect::<Vec<_>>();
        // kbe.E.extend(top_cps);
        // println!("Top 5 critical pairs:");
        // for (l, r) in top_cps.iter() {
        //     println!("  {} -> {}", strterm(l), strterm(r));
        // }


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
