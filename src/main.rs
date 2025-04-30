mod term_rewrite;
mod types;
mod util;
mod kbo;

use std::collections::HashMap;
use std::collections::HashSet;

use bimap::BiMap;
use term_rewrite::parseeqs;

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



#[derive(Debug, Clone,PartialEq, Eq, Hash)]
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

struct KBEGraph {
    C:  BiMap<Id, ENode>, // can be done as Vec<ENode> with id as index, and an additional C_inv
    id_count: usize,
    E: EquationSet,
    R: RuleSet,
}

fn main() {

    let mut kbe = KBEGraph {
        C: BiMap::new(),
        id_count: 0,
        E: vec![],
        R: vec![],
    };

    // Step 0
    let pre: Precedence = vec![
        (String::from("I"), 3),
        (String::from("M"), 1),
        (String::from("E"), 2),
    ];
    let lpo = |t: &Term, t_prime: &Term| lpo_gt(&pre, t, t_prime);


    // Step 1
    fn insert_term(t: &Term, kbe: &mut KBEGraph) -> Id {
        match t {
            Term::Variable(var) => {
                // variable becomes a leaf (recursive calls will handle parents)
                let node = ENode {
                    label: var.0.clone(),
                    children: vec![],
                };
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

    // let t = parseterm("M(I(M(y,M(x, M(I(x), I(y))))),z)"); // -> z
    let t = parseterm("M(I(M(b,M(a, M(I(a), I(b))))),c)"); // -> c
    let t_id = insert_term(&t, &mut kbe);

    // Step 2
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


}
