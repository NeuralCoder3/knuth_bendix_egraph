mod term_rewrite;
mod types;
mod util;
mod kbo;

use std::cell::RefCell;
use std::cmp;
use std::collections::HashMap;
use std::collections::HashSet;
use std::error::Error;
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;
use std::str::FromStr;

use term_rewrite::parseeqs;
use term_rewrite::uniquevar;

use crate::term_rewrite::*;
use crate::types::*;
use crate::kbo::*;


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
        // let (rules, eqs) = new_state;
        let new_state_prime = knuth_steps(verbose, lpo, &new_state);
        if new_state != new_state_prime {
            changed = true;
            new_state = new_state_prime;
        }
    }
    new_state
}



// some id:usize outside, with map (C) usize -> Node  (bidirectional)
// term -> id: construct analogous nod, look up in inverse C

#[derive(Debug, Clone)]
struct RawNode {
    label: String,
    children: Vec<Node>,
    // TODO: handle multiple parents
}
// type Node = Rc<RefCell<RawNode>>; // RefCell needed to set parent children pointer
type Node = RawNode;

fn Node(label: String, children: Vec<Node>) -> Node {
    let node = RawNode {
        label,
        children: children.clone(),
    };
    node
}

struct KBEGraph {
    embedding: HashMap<Term, Node>, // TODO: only 
    roots: Vec<Node>, // we can use keys of C instead
}

// the caller is responsible for the roots
fn embed(t: &Term, dag: &mut KBEGraph) -> Node {
    // lookup in graph
    if let Some(node) = dag.embedding.get(t) {
        return node.clone();
    }
    match t {
        Term::Variable(var) => {
            // variable becomes a leaf (recursive calls will handle parents)
            let node = Node(var.0.clone(), vec![]);
            dag.embedding.insert(t.clone(), node.clone());
            return node;
        }
        Term::Function(f, ts) => {
            // embed all children, then create a new node (keep track of parent)
            let mut children = vec![];
            for t_prime in ts {
                let child = embed(t_prime, dag);
                children.push(child);
            }
            let node = Node(f.clone(), children.iter().cloned().collect());
            dag.embedding.insert(t.clone(), node.clone());
            return node;
        }
    }
}

fn ground_instances(dag: &KBEGraph) -> Vec<Term> {
    // term instance and subterm
    fn aux(node: Node) -> (Term, Vec<Term>) {
        let subs: Vec<(Term, Vec<Term>)> = node
            .children
            .iter()
            .map(|child| aux(child.clone()))
            .collect();
        let direct_subterms: Vec<Term> = subs.iter().map(|(t, _)| t.clone()).collect();
        let subterms: Vec<Term> = subs
            .iter()
            .map(|(_, subterms)| subterms.clone())
            .flatten()
            .chain(direct_subterms.iter().cloned())
            .collect();
        let term = Term::Function(
            node.label.clone(),
            subs.iter().map(|(t, _)| t.clone()).collect(),
        );
        (term, subterms)
    }
    // dag.roots.iter().map(|root| aux(root.clone())).map(|(t, subterms)| vec![t].into_iter().chain(subterms.into_iter()).collect()).flatten().collect()

    let mut instances = vec![];
    for root in dag.roots.iter() {
        let (t, subterms) = aux(root.clone());
        instances.push(t);
        for subterm in subterms {
            instances.push(subterm);
        }
    }
    instances
}

fn node_match_term(node: &Node, t: &Term) -> bool {
    match t {
        Term::Variable(var) => node.label == var.0,
        Term::Function(f, ts) => {
            if node.label != f.clone() {
                return false;
            }
            if node.children.len() != ts.len() {
                return false;
            }
            for (child, t_prime) in node.children.iter().zip(ts.iter()) {
                if !node_match_term(child, t_prime) {
                    return false;
                }
            }
            true
        }
    }
}

fn simplify_dag_with_rule(dag: &mut KBEGraph, rule: &Rule) -> bool {
    // if changed => new node and the children of the old node
    fn aux(node: &mut Node, dag: &mut KBEGraph, rule: &Rule) -> (bool,Option<(Node, Vec<Node>)>) {
        let mut changed = false;
        for i in 0..node.children.len() {
            // TODO: at this point, a reading reference to node exists => problem
            let (child_changed, new_node) = aux(&mut node.children[i], dag, rule);
            changed |= child_changed;
            if let Some((new_node, children)) = new_node {
                changed = true;
                // update children
                node.children[i] = new_node.clone();
                // update parents
                // for child in children.iter() {
                //     child.borrow_mut().parents.retain(|parent| !Rc::ptr_eq(parent, node));
                // }
                // new_node.borrow_mut().parents.push(node.clone());
            }
        }

        // let mut changed = false;
        // top up
        if node_match_term(node, &rule.0) {
            // apply rule
            // (rule destination is already simplified by KBO)
            let new_node = embed(&rule.1, dag);
            // only update if not root (set children of parents to new node)
            // for parent_pointer in node.borrow().parents.iter() {
            //     let mut parent = parent_pointer.borrow_mut();
            //     let i = parent
            //         .children
            //         .iter()
            //         .position(|child| Rc::ptr_eq(child, node))
            //         .unwrap();
            //     parent.children[i] = new_node.clone();
            //     new_node.borrow_mut().parents.push(parent_pointer.clone());
            // }
            // // old children have to be preserved (thus becoming roots / are detached from the node)
            for child in node.children.iter() {
                dag.roots.push(child.clone());
            //     // no pointer comparison for clone reasons and we should never have two different identical nodes
            //     child.borrow_mut().parents.retain(|parent| parent != node);
            }
            // TODO: remove node from graph (roots)
            // changed = true;
            // visit all new roots recursively (that is the default -> drop down to else)

            return (true,Some ((new_node, node.children.clone())));
        }

        (changed,None)
        // None


        // for child in node.borrow().children.iter() {
        //     aux(child, dag, rule);
        // }
        // node.borrow().children.clone().iter().for_each(|child| {
        //     changed |= aux(&child, dag, rule);
        // });
        // changed
    }

    // TODO: not clone
    let orig_roots = dag.roots.clone();
    let mut changed = false;
    for mut root in orig_roots.into_iter() {
        changed |= aux(&mut root, dag, rule).0;
    }
    changed
}

// expect grounded rules
fn simplify_dag(dag: &mut KBEGraph, rules: &RuleSet, ground_instances: &Vec<Term>) -> RuleSet {
    let mut output = vec![];
    for rule in rules.iter() {
        let (l, r) = rule;
        // instantiate all variables from l with some ground instance
        // apply rule via simplify_dag_with_rule
        let vars = vars(l)
            .iter()
            .cloned()
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let insts = instantiations(&vars, &ground_instances);
        for inst in insts.iter() {
            let l_inst = subst(inst, l);
            let r_inst = subst(inst, r);
            let rule_inst = (l_inst, r_inst);
            let changed = simplify_dag_with_rule(dag, &rule_inst);
            if changed {
                output.push(rule_inst);
            }
        }
    }
    output
}

fn instantiations(vars: &Vec<VarSym>, t: &Vec<Term>) -> Vec<SubstitutionSet> {
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

fn main() {
    let pre: Precedence = vec![
        (String::from("I"), 3),
        (String::from("M"), 1),
        (String::from("E"), 2),
    ];
    let mut eqs: EquationSet = parseeqs(vec!["M(M(x,y),z)=M(x,M(y,z))", "M(I(x),x)=E", "M(E,x)=x"]);
    //     { I(M(x, y)) -> M(I(y), I(x))
    //   M(x, M(I(x), z)) -> z
    //   M(x, I(x)) -> E
    //   I(I(x)) -> x
    //   I(E) -> E
    //   M(x, E) -> x
    //   M(I(x), M(x, z)) -> z
    //   M(M(x, y), z) -> M(x, M(y, z))
    //   M(I(x), x) -> E
    //   M(E, x) -> x }

    // test knuth_bendix_completion
    // let rules = knuth_bendix_completion_verbose_precedence(&pre, eqs);
    // let t = parseterm("M(I(M(y,M(x, M(I(x), I(y))))),z)"); // -> z
    // let t_prime = linorm(&rules, &t);
    // println!("{}", strterm(&t_prime));

    let mut rules: RuleSet = vec![];
    // let state = (rules, eqs);

    // let t = parseterm("M(I(M(y,M(x, M(I(x), I(y))))),z)"); // -> z
    let t = parseterm("M(I(M(b,M(a, M(I(a), I(b))))),c)"); // -> c

    // Step 0
    let lpo = |t: &Term, t_prime: &Term| lpo_gt(&pre, t, t_prime);
    // we changed (by init) our R/E, so KBO
    // #[cfg(use_knuth)]
    // {
        let state = knuth_loop(true, &lpo, (rules, eqs));
        rules = state.0;
        eqs = state.1;
    // }

    let t_prime = linorm(&rules, &t);
    println!("Rules:");
    printrules(&rules);
    println!("Equations:");
    printeqs(&eqs);
    println!("Result:");
    println!("{}", strterm(&t_prime));

    // Step 1
    // we have an ast but keep all old nodes (in a normalized form) as DAG
    // => we want to not overlook possible equalities on old forms

    // Node = { label: Symbol, children: Vec<Node> }
    // a translation function (that also simplifies -- memoization): map : Term -> Node
    // (maybe) a set of roots: R : Set<Node>
    // a parent map: parent : Node -> Node (necessary for rule application)
    // functions on our DAG
    // embed: Term -> Node
    // simplify, applies rules to the tree
    // f _(*(2,x))_ -> f _(>>(x,1))_
    // but also g _(*(2,x))_ -> g _(>>(x,1))_
    // => rewrite *(2,x) to >>(x,1), delete the * node, keep the 2 node
    // update the parent pointers

    // we identify the graph by its embedding of terms
    let mut dag = KBEGraph {
        embedding: HashMap::new(),
        roots: vec![],
    };

    // Note: our graph is grounded, our rules not necessarily
    let t_node = embed(&t, &mut dag);
    dag.roots.push(t_node.clone());

    // Step 2
    // we have init R, E in Step 0

    // Step 3
    for i in 0..5 {
        println!();
        println!();
        println!("Iteration {}", i);
        // Step 3.1 (e-graph phase)
        // TODO: match using rules (can they ever apply?)/equations (as rules both sides), add ground equations (oriented to R)
        // Answer: either we need to full unify-match the rules or we handle them all in Step 3.1

        // normalize left side of rule, match on AST

        // fn is_grounded(t: &Term) -> bool {
        //     match t {
        //         Term::Variable(_) => false,
        //         Term::Function(_, ts) => ts.iter().all(|t| is_grounded(t)),
        //     }
        // }

        // let mut ground_instances = vec![];

        let ground_instances = ground_instances(&dag);
        println!("Number of ground instances: {}", ground_instances.len());
        for t in ground_instances.iter() {
            println!("  {}", strterm(t));
        }

        // rules + ->eq + <-eq
        rules.extend(simplify_dag(&mut dag, &rules, &ground_instances));
        rules.extend(simplify_dag(&mut dag, &eqs.iter().map(|(l, r)| (l.clone(), r.clone())).collect(), &ground_instances));
        rules.extend(simplify_dag(&mut dag, &eqs.iter().map(|(l, r)| (r.clone(), l.clone())).collect(), &ground_instances));

        // for rule in rules.iter() {
        //     let (l, r) = rule;
        //     // instantiate all variables from l with some ground instance
        //     // apply rule via simplify_dag_with_rule
        //     let vars = vars(l)
        //         .iter()
        //         .cloned()
        //         .collect::<HashSet<_>>()
        //         .into_iter()
        //         .collect::<Vec<_>>();
        //     let insts = instantiations(&vars, &ground_instances);
        //     for inst in insts.iter() {
        //         let l_inst = subst(inst, l);
        //         let r_inst = subst(inst, r);
        //         let rule_inst = (l_inst, r_inst);
        //         simplify_dag_with_rule(&mut dag, &rule_inst);
        //     }
        // }

        // Step 3.2 (KBO)
        // get critical pairs, select promising ones for E

        // for i in 0..5 {
        let mut cps = vec![];
        for rule1 in rules.iter() {
            for rule2 in rules.iter() {
                let cp = critical_pair(rule1, rule2);
                cps.extend(cp);
            }
        }
        // println!("Critical pairs:");
        // for (l, r) in cps.iter() {
        //     println!("{} ! {}", strterm(l), strterm(r));
        // }

        // #[cfg(use_knuth)]
        // {
            // TODO: only add some critical pairs (ematch or grounded)
            eqs.extend(cps);
            let state = knuth_loop(true, &lpo, (rules, eqs));
            rules = state.0;
            eqs = state.1;
        // }
        println!("Rules:");
        printrules(&rules);
        println!("Equations:");
        printeqs(&eqs);

        println!("Result:");
        let t_prime = linorm(&rules, &t);
        println!("{}", strterm(&t_prime));
    }
}
