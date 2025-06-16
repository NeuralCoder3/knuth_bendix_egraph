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
}

/*
    insert a term into the KBE graph
*/
fn insert_term(t: &Term, kbe: &mut KBEGraph) -> Id {
    match t {
        Term::Variable(var) => { // TODO: panic? term should be grounded
            // variable becomes a leaf (recursive calls will handle parents)
            let node = ENode {
                label: var.0.clone(),
                children: vec![],
            };
            #[allow(non_snake_case)]
            let C = &mut kbe.C;
            if let Some(id) = C.get_by_right(&node) {
                return id.clone();
            }
            let id = kbe.id_count;
            kbe.id_count += 1;
            C.insert_no_overwrite(id, node).unwrap();
            return id;
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

fn extract_term(
    kbe: &KBEGraph,
    id: Id,
) -> Term {
    let node = kbe.C.get_by_left(&id).unwrap();
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
        let child_node = kbe.C.get_by_left(child).unwrap();
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
fn rewriteRule(rule: &Rule) {}

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
                    let child = kbe.C.get_by_left(id).unwrap();
                    match_rule(kbe, t, child)
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
    rules: &RuleSet, // grounded rules
) -> RuleSet {
    let mut applied = vec![];
    for (id, node) in kbe.C.iter() {
        let applicable = rules.iter()
            .filter(|(l, _)| {
                match_rule(kbe, l, node)
            });
        applied.extend(
            // TODO: double map not necessary
            applicable.map(|rule| {
                // TODO: clone not necessary
                (id.clone(), rule)
            })
        );
    }

    // replace id by (embedded) right term
    for (i, rule) in applied.iter() {
        let (l, r) = rule;
        let r_id = insert_term(r, kbe);
        let node = kbe.C.get_by_left(&r_id).unwrap().clone(); // TODO: clone necessary as owner is bound to kbe
        // unassociate r_id
        kbe.C.remove_by_left(&r_id);
        kbe.C.insert(i.clone(), node.clone());
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
    return applied.into_iter().map(|(_, rule)| {
        rule.clone() // TODO: clone not necessary
    }).collect::<Vec<_>>();
}

fn simplify_dag(kbe: &mut KBEGraph, ground_instances: &HashSet<Term>) -> RuleSet {
    let mut new_rules = vec![];
    let lr_eqs = kbe
        .E
        .iter()
        .map(|(l, r)| (l.clone(), r.clone()))
        .collect::<Vec<_>>();
    let rl_eqs = kbe
        .E
        .iter()
        .map(|(l, r)| (r.clone(), l.clone()))
        .collect::<Vec<_>>();
    let rules = kbe
        .R
        .iter()
        .chain(lr_eqs.iter())
        .chain(rl_eqs.iter())
        .collect::<Vec<_>>();
    // let mut i = 0;
    for rule in rules.iter() {
        // println!("Rule {}: {:?}", i, rule);
        // i += 1;
        let (l, r) = rule;
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
            let rule_inst = (l_inst, r_inst);
            new_rules.push(rule_inst.clone());
            // let changed = simplify_dag_with_rule(dag, &rule_inst);
            // if changed {
            //     output.push(rule_inst);
            // }
        }
    }
    // return new_rules
    // only add the applicable ones
    // return vec![];
    return apply_rules(kbe, &new_rules);
    // return new_rules.iter().flat_map(|rule| {
    //     apply_rules(kbe, rules)
    // }).collect::<Vec<_>>();
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

fn main() {
    let mut kbe = KBEGraph {
        C: BiMap::new(),
        id_count: 0,
        E: vec![],
        R: vec![],
    };

    // Step 0 (define precedence)
    let pre: Precedence = vec![
        (String::from("I"), 3),
        (String::from("M"), 1),
        (String::from("E"), 2),
    ];
    let lpo = |t: &Term, t_prime: &Term| lpo_gt(&pre, t, t_prime);

    // Step 1 (build KBE graph)

    // let t = parseterm("M(I(M(y,M(x, M(I(x), I(y))))),z)"); // -> z
    // let t = parseterm("M(I(M(b,M(a, M(I(a), I(b))))),c)"); // -> c
    let t = parseterm("M(I(a), M(a, b))"); // -> z
    let t_id = insert_term(&t, &mut kbe);

    // Step 2 (orient rules in initial KBO step)
    kbe.E = parseeqs(vec!["M(M(x,y),z)=M(x,M(y,z))", "M(I(x),x)=E", "M(E,x)=x"]);
    kbe.R = vec![];
    let state = knuth_loop(true, &lpo, (kbe.R, kbe.E));
    kbe.R = state.0;
    kbe.E = state.1;

    let t_prime = linorm(&kbe.R, &t);
    println!("Rules:");
    printrules(&kbe.R);
    println!("Equations:");
    printeqs(&kbe.E);
    println!("Result:");
    println!("{}", strterm(&t_prime));

    // Step 3 (loop)
    for i in 0..5 {
        println!();
        println!();
        println!("Iteration {}", i);

        // Step 3.1 (E-Graph: Apply rules on graph)
        // TODO: without 3.2 this would not resolve as equations are oriented
        // we would just eagerly rewrite the graph? (adding rules to R help? or that we keep the subexpressions?)
        // let ground_instances = ground_instances(&kbe);
        let mut instances: HashSet<Term> = HashSet::new();
        let mut visited: HashMap<ENode, Term> = HashMap::new();
        for (_, enode) in kbe.C.iter() {
            // b
            let _ = ground_instances(&mut visited, &mut instances, enode, &kbe);
        }
        println!("Number of ground instances: {}", instances.len());
        for t in instances.iter() {
            println!("  {}", strterm(t));
        }
        // TODO: also at rewrite order
        // add all instances to E, knuth bendix (orient, simpl)
        // or only if left/right in C

        // is from E already onriented/grounded is oriented

        // // rules + ->eq + <-eq
        let new_rules = simplify_dag(&mut kbe, &instances);
        println!("New rules:");
        printrules(&new_rules);
        // kbe.R.extend(new_rules);
        kbe.E.extend(new_rules);

        // Step 3.2 (KBO: Add critical pairs)
        let mut cps = vec![];
        for rule1 in kbe.R.iter() {
            for rule2 in kbe.R.iter() {
                let cp = critical_pair(rule1, rule2);
                cps.extend(cp);
            }
        }
        println!("Computed {} critical pairs", cps.len());
        // TODO: only add some critical pairs (ematch or grounded (how many from R are subsumed))
        // kbe.E.extend(cps);
        // simp via R, match on C

        // kbo faster because only considers relevant critical pairs
        let state = knuth_loop(true, &lpo, (kbe.R, kbe.E));
        kbe.R = state.0;
        kbe.E = state.1;

        println!("Intermediate State:");
        println!("Rules:");
        printrules(&kbe.R);
        println!("Equations:");
        printeqs(&kbe.E);
        

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
