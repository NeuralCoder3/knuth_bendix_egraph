mod term_rewrite;
mod types;
mod util;

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

/// Error type indicating that completion failed.
#[derive(Debug)]
pub struct CompletionFailed;

impl fmt::Display for CompletionFailed {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CompletionFailed")
    }
}

impl Error for CompletionFailed {}

//
// Unification
//

/// Attempts to unify terms `t` and `t_prime` under the current substitution `subst`.
/// Returns `Some(new_subst)` if successful, or `None` if unification fails.
fn unify_with_subst(
    subst_var: &SubstitutionSet,
    t: &Term,
    t_prime: &Term,
) -> Option<SubstitutionSet> {
    match t {
        Term::Variable(var) => {
            match t_prime {
                Term::Variable(var_prime) if var == var_prime => Some(subst_var.clone()),
                _ if vars(t_prime).contains(var) => None, // Occurs check
                _ => {
                    // Extend the substitution with (var -> t_prime) and update all mappings.
                    let mut new_subst = vec![(var.clone(), t_prime.clone())];
                    new_subst.extend(subst_var.iter().map(|(x, a)| {
                        (x.clone(), subst(&vec![(var.clone(), t_prime.clone())], a))
                    }));
                    Some(new_subst)
                }
            }
        }
        Term::Function(f, ts) => match t_prime {
            Term::Variable(var_prime) => {
                if vars(t).contains(var_prime) {
                    None
                } else {
                    let mut new_subst = vec![(var_prime.clone(), t.clone())];
                    new_subst.extend(subst_var.iter().map(|(x, a)| {
                        (x.clone(), subst(&vec![(var_prime.clone(), t.clone())], a))
                    }));
                    Some(new_subst)
                }
            }
            Term::Function(f_prime, ts_prime) if f == f_prime => {
                unify_term_lists(subst_var.clone(), ts, ts_prime)
            }
            _ => None,
        },
    }
}

/// Unifies two lists of terms under the current substitution.
fn unify_term_lists(
    subst_var: SubstitutionSet,
    terms1: &[Term],
    terms2: &[Term],
) -> Option<SubstitutionSet> {
    if terms1.len() != terms2.len() {
        return None;
    }
    if terms1.is_empty() {
        return Some(subst_var);
    }
    let new_subst = unify_with_subst(&subst_var, &terms1[0], &terms2[0])?;
    let new_terms1: Vec<Term> = terms1[1..].iter().map(|t| subst(&new_subst, t)).collect();
    let new_terms2: Vec<Term> = terms2[1..].iter().map(|t| subst(&new_subst, t)).collect();
    unify_term_lists(new_subst, &new_terms1, &new_terms2)
}

/// A convenience function to unify two terms starting with an empty substitution.
/// (The resulting substitution is “reversed”)
fn unify(t: &Term, t_prime: &Term) -> Option<SubstitutionSet> {
    let mut s = unify_with_subst(&vec![], t, t_prime)?;
    s.reverse();
    Some(s)
}

//
// Critical Pair Computation
//

/// Computes parts of a critical pair from `term` and a rewrite rule `(l -> r)`.
/// Returns a vector of pairs `(t, subst)` representing a potential overlap.
fn critical_pair_parts(term: &Term, rule: &Rule) -> Vec<(Term, SubstitutionSet)> {
    match term {
        Term::Variable(_) => vec![],
        Term::Function(f, ts) => {
            let (l, r) = rule;
            let mut result = Vec::new();
            if let Some(s) = unify(term, l) {
                result.push((r.clone(), s));
            }
            let parts_list = critical_pair_parts_list(ts, rule);
            for (ts_prime, s) in parts_list {
                result.push((Term::Function(f.clone(), ts_prime), s));
            }
            result
        }
    }
}

/// Computes critical pair parts for a list of subterms given a rewrite rule.
fn critical_pair_parts_list(ts: &[Term], rule: &Rule) -> Vec<(Vec<Term>, SubstitutionSet)> {
    if ts.is_empty() {
        vec![]
    } else {
        let mut results = Vec::new();
        let first = &ts[0];
        let rest = &ts[1..];
        for (t_prime, s) in critical_pair_parts(first, rule) {
            let mut new_ts = vec![t_prime];
            new_ts.extend_from_slice(rest);
            results.push((new_ts, s));
        }
        for (mut ts_prime, s) in critical_pair_parts_list(rest, rule) {
            let mut new_ts = vec![first.clone()];
            new_ts.append(&mut ts_prime);
            results.push((new_ts, s));
        }
        results
    }
}

/// Applies the substitution contained in each pair to both a term and the rule’s right–hand side.
fn apply_cp_subst(r: &Term, pairs: Vec<(Term, SubstitutionSet)>) -> Vec<(Term, Term)> {
    pairs
        .into_iter()
        .map(|(t, s)| (subst(&s, &t), subst(&s, r)))
        .collect()
}

/// Removes symmetric duplicates from a vector of pairs.
fn remove_symmetric_duplicates(pairs: Vec<(Term, Term)>) -> Vec<(Term, Term)> {
    let mut result = Vec::new();
    for pair in pairs.into_iter() {
        let (ref x, ref y) = pair;
        if !result
            .iter()
            .any(|(a, b)| (a == y && b == x) || (a == x && b == y))
        {
            result.push(pair);
        }
    }
    result
}

/// Computes the critical pair between two rules.
/// First renames variables apart via `uniquevar` (assumed to be defined),
/// then returns the union of the critical pair components (with symmetric duplicates removed).
fn critical_pair(rule1: &Rule, rule2: &Rule) -> Vec<(Term, Term)> {
    // Assume that `uniquevar` takes a pair of rules and returns a pair with variables renamed apart.
    let (rule1_prime, rule2_prime) = uniquevar(rule1, rule2);
    let (l1, r1) = &rule1_prime;
    let (l2, r2) = &rule2_prime;
    let mut pairs = Vec::new();
    pairs.extend(apply_cp_subst(r1, critical_pair_parts(l1, &rule2_prime)));
    pairs.extend(apply_cp_subst(r2, critical_pair_parts(l2, &rule1_prime)));
    remove_symmetric_duplicates(pairs)
}

//
// Lexicographic Path Ordering (LPO)
//

/// Returns `true` if symbol `x` has higher precedence than `y` according to `pre`.
fn symbol_greater(pre: &Precedence, x: &FunSym, y: &FunSym) -> bool {
    let i = pre.iter().find(|(sym, _)| sym == x).map(|(_, p)| *p);
    let j = pre.iter().find(|(sym, _)| sym == y).map(|(_, p)| *p);
    match (i, j) {
        (Some(i), Some(j)) => i > j,
        _ => false,
    }
}

/// Returns `true` if `x` and `y` are the same symbol or have equal precedence.
fn symbol_equal(pre: &Precedence, x: &FunSym, y: &FunSym) -> bool {
    if x == y {
        true
    } else {
        let i = pre.iter().find(|(sym, _)| sym == x).map(|(_, p)| *p);
        let j = pre.iter().find(|(sym, _)| sym == y).map(|(_, p)| *p);
        match (i, j) {
            (Some(i), Some(j)) => i == j,
            _ => false,
        }
    }
}

/// Defines a strict order from `greq` by ensuring that `y` is not greater than `x`.
fn strictly_greater<F>(greq: F, x: &Term, y: &Term) -> bool
where
    F: Fn(&Term, &Term) -> bool,
{
    greq(x, y) && !greq(y, x)
}

/// Returns `true` if `x` and `y` are equivalent under ordering `greq`.
fn equivalent_by_order<F>(greq: F, x: &Term, y: &Term) -> bool
where
    F: Fn(&Term, &Term) -> bool,
{
    greq(x, y) && greq(y, x)
}

/// Extends the ordering `greq` lexicographically to lists of terms.
fn lexicographic_greq<F>(greq: &F, xs: &[Term], ys: &[Term]) -> bool
where
    F: Fn(&Term, &Term) -> bool,
{
    if xs.is_empty() {
        ys.is_empty()
    } else if ys.is_empty() {
        true
    } else {
        let x = &xs[0];
        let y = &ys[0];
        if strictly_greater(greq, x, y) {
            true
        } else if equivalent_by_order(greq, x, y) {
            lexicographic_greq(greq, &xs[1..], &ys[1..])
        } else {
            false
        }
    }
}

/// The lexicographic path ordering (LPO) “greater–or–equal” relation with respect to `pre`.
fn lpo_ge(pre: &Precedence, t: &Term, t_prime: &Term) -> bool {
    match (t, t_prime) {
        (_, Term::Variable(var_prime)) => vars(t).contains(var_prime),
        (Term::Variable(_), _) => false,
        (Term::Function(f, ts), Term::Function(f_prime, ts_prime)) => {
            let option1 = symbol_equal(pre, f, f_prime)
                && lexicographic_greq(&|a, b| lpo_ge(pre, a, b), ts, ts_prime)
                && ts_prime.iter().all(|tpp| lpo_gt(pre, t, tpp));
            let option2 =
                symbol_greater(pre, f, f_prime) && ts_prime.iter().all(|tpp| lpo_gt(pre, t, tpp));
            let option3 = ts.iter().any(|tpp| lpo_ge(pre, tpp, t_prime));
            option1 || option2 || option3
        }
    }
}

/// The strict part of `lpo_ge`.
fn lpo_gt(pre: &Precedence, t: &Term, t_prime: &Term) -> bool {
    lpo_ge(pre, t, t_prime) && !lpo_ge(pre, t_prime, t)
}

//
// Completion Procedures
//

/// Returns the complexity of a rule, defined as the maximum number of nodes in its sides.
fn rule_complexity(rule: &Rule) -> usize {
    let (l, r) = rule;
    cmp::max(nodes(l), nodes(r))
}

/// Orients an equation into a rewrite rule using the ordering `lpo`.
/// Filters for orientable equations and chooses one with minimal complexity.
/// Returns the oriented rule together with the current rules and the remaining equations.
fn orient_equation<F>(
    lpo: &F,
    state: (RuleSet, EquationSet),
) -> Result<(Rule, RuleSet, EquationSet), CompletionFailed>
where
    F: Fn(&Term, &Term) -> bool,
{
    let (rules, eqs) = state;
    let orientable: Vec<Equation> = eqs
        .iter()
        .cloned()
        .filter(|(l, r)| lpo(l, r) || lpo(r, l))
        .collect();
    if orientable.is_empty() {
        return Err(CompletionFailed);
    }
    let chosen = orientable
        .into_iter()
        .reduce(|eq1, eq2| {
            if rule_complexity(&eq1) <= rule_complexity(&eq2) {
                eq1
            } else {
                eq2
            }
        })
        .unwrap();
    let (l, r) = chosen.clone();
    let new_rule = if lpo(&l, &r) {
        (l.clone(), r.clone())
    } else {
        (r.clone(), l.clone())
    };
    let new_eqs: EquationSet = eqs.into_iter().filter(|e| *e != chosen).collect();
    Ok((new_rule, rules, new_eqs))
}

/// Normalizes the right–hand sides of `rules` using the new rule `r`.
fn compose((r, rules, eqs): (Rule, RuleSet, EquationSet)) -> (Rule, RuleSet, EquationSet) {
    let mut r_and_rules = vec![r.clone()];
    r_and_rules.extend(rules.clone());
    let new_rules: RuleSet = rules
        .into_iter()
        .map(|(l, r_prime)| (l, linorm(&r_and_rules, &r_prime)))
        .collect();
    (r, new_rules, eqs)
}

/// Adds all critical pairs deducible from `r` (with each rule in `r :: rules`)
/// to the set of equations.
fn deduce_critical_pairs(
    (r, rules, eqs): (Rule, RuleSet, EquationSet),
) -> (Rule, RuleSet, EquationSet) {
    let mut new_eqs = eqs;
    let mut r_and_rules = vec![r.clone()];
    r_and_rules.extend(rules.clone());
    for rule in r_and_rules.iter() {
        let cp = critical_pair(&r, rule);
        new_eqs.extend(cp);
    }
    (r, rules, new_eqs)
}

/// Removes rules from `rules` whose left–hand side is contained in the left–hand side of `rule`.
fn collapse((rule, rules, eqs): (Rule, RuleSet, EquationSet)) -> (Rule, RuleSet, EquationSet) {
    let (l, _) = &rule;
    let new_rules: RuleSet = rules
        .into_iter()
        .filter(|(l_prime, _)| !contain(l, l_prime))
        .collect();
    (rule, new_rules, eqs)
}

/// Adds the new rule `r` to the set of rules.
fn add_rule((r, rules, eqs): (Rule, RuleSet, EquationSet)) -> (RuleSet, EquationSet) {
    let mut new_rules = rules;
    new_rules.insert(0, r);
    (new_rules, eqs)
}

/// Normalizes both sides of every equation in `eqs` using the current rules.
fn simplify((rules, eqs): (RuleSet, EquationSet)) -> (RuleSet, EquationSet) {
    let new_eqs: EquationSet = eqs
        .into_iter()
        .map(|(l, r)| (linorm(&rules, &l), linorm(&rules, &r)))
        .collect();
    (rules, new_eqs)
}

/// Removes trivial equations (where both sides are equal). If `verbose` is true,
/// duplicate equations are also removed via `distincteqs`.
fn remove_trivial(verbose: bool, (rules, eqs): (RuleSet, EquationSet)) -> (RuleSet, EquationSet) {
    let eqs = if verbose { distincteqs(eqs) } else { eqs };
    let new_eqs: EquationSet = eqs.into_iter().filter(|(l, r)| l != r).collect();
    (rules, new_eqs)
}

/// Performs one Knuth–Bendix completion step on the current state using ordering `lpo`.
fn completion_step<F>(
    verbose: bool,
    lpo: &F,
    state: (RuleSet, EquationSet),
) -> (RuleSet, EquationSet)
where
    F: Fn(&Term, &Term) -> bool,
{
    let oriented = orient_equation(lpo, state).expect("CompletionFailed");
    let composed = compose(oriented);
    let deduced = deduce_critical_pairs(composed);
    let collapsed = collapse(deduced);
    let added = add_rule(collapsed);
    let simplified = simplify(added);
    let removed = remove_trivial(verbose, simplified);
    removed
}

//
// Printing Functions
//

fn print_input(eqs: &EquationSet) {
    println!("================ Input ==================");
    printeqs(eqs);
}

fn print_step(n: usize, rules: &RuleSet, eqs: &EquationSet) {
    println!("================ Step {} =================", n);
    printeqs(eqs);
    println!();
    printrules(rules);
}

fn print_output(n: usize, rules: &RuleSet) {
    println!("============== Complete {} ==============", n);
    printrules(rules);
}

//
// Knuth–Bendix Completion Loop
//

/// Repeatedly applies completion steps until there are no equations left.
/// If `verbose` is true, intermediate states are printed.
fn completion_loop<F>(
    verbose: bool,
    mut n: usize,
    lpo: &F,
    mut state: (RuleSet, EquationSet),
) -> RuleSet
where
    F: Fn(&Term, &Term) -> bool,
{
    if n == 0 {
        if verbose {
            print_input(&state.1);
        }
        state = completion_step(verbose, lpo, state);
        n = 1;
    }
    loop {
        let (ref rules, ref eqs) = state;
        if eqs.is_empty() {
            let rules_prime: RuleSet = rules.iter().map(|r| decvarsub(r)).collect();
            if verbose {
                print_output(n, &rules_prime);
            }
            return rules_prime;
        } else {
            if verbose {
                print_step(n, rules, eqs);
            }
            state = completion_step(verbose, lpo, state);
            n += 1;
        }
    }
}

/// Runs the Knuth–Bendix completion algorithm with ordering `lpo` and initial equations `eqs`.
fn knuth_bendix_completion<F>(lpo: &F, eqs: EquationSet) -> RuleSet
where
    F: Fn(&Term, &Term) -> bool,
{
    let initial_state = remove_trivial(false, (vec![], eqs));
    completion_loop(false, 0, lpo, initial_state)
}

/// Runs completion using the ordering induced by the precedence `pre`.
fn knuth_bendix_completion_precedence(pre: &Precedence, eqs: EquationSet) -> RuleSet {
    knuth_bendix_completion(&|t, t_prime| lpo_gt(pre, t, t_prime), eqs)
}

/// Runs the Knuth–Bendix completion algorithm with verbose output.
fn knuth_bendix_completion_verbose<F>(lpo: &F, eqs: EquationSet) -> RuleSet
where
    F: Fn(&Term, &Term) -> bool,
{
    let initial_state = remove_trivial(false, (vec![], eqs));
    completion_loop(true, 0, lpo, initial_state)
}

/// Runs the verbose completion version with an ordering induced by `pre`.
fn knuth_bendix_completion_verbose_precedence(pre: &Precedence, eqs: EquationSet) -> RuleSet {
    knuth_bendix_completion_verbose(&|t, t_prime| lpo_gt(pre, t, t_prime), eqs)
}

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

#[derive(Hash, Debug, PartialEq, Eq)]
struct RawNode {
    label: String,
    children: Vec<Node>,
    // children: Vec<Rc<Node>>,
}
// type Node = Rc<RefCell<RawNode>>; // RefCell needed to set parent children pointer
#[derive(Debug, Clone)]
struct Node {
    id: u32,
    content: Rc<RefCell<RawNode>>,
}
impl Node {
    fn new(dag:&mut KBEGraph, label: String, children: Vec<Node>) -> Node {
        let id = dag.nodecount;
        dag.nodecount += 1;
        Node {
            id,
            content: Rc::new(RefCell::new(RawNode {
                label,
                children,
            })),
        }
    }

    fn label(&self) -> String {
        self.content.borrow().label.clone()
    }

    fn label_ref(&self) -> std::cell::Ref<'_, String> {
        std::cell::Ref::map(self.content.borrow(), |raw| &raw.label)
    }

    fn children(&self) -> std::vec::Vec<Node> {
        self.content.borrow().children.clone()
    }

    fn children_ref(&self) -> std::cell::Ref<'_, std::vec::Vec<Node>> {
        std::cell::Ref::map(self.content.borrow(), |raw| &raw.children)
    }

    // fn new(dag:&mut KBEGraph, content: RawNode) -> Node {
    //     let id = dag.nodecount;
    //     dag.nodecount += 1;
    //     Node {
    //         id,
    //         content: Rc::new(RefCell::new(content)),
    //     }
    // }
}
impl Hash for Node {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Node { }

struct KBEGraph {
    embedding: HashMap<Term, Node>,
    roots: HashSet<Node>,
    parent: HashMap<Node, (usize,Node)>,
    nodecount: u32,
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
            let node = Node::new(dag,
                var.0.clone(),
                vec![],
            );
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
            let node = Node::new(
                dag,
                f.clone(),
                children.iter().cloned().collect(),
            );
            for (i, child) in children.into_iter().enumerate() {
                dag.parent.insert(child, (i as usize, node.clone()));
            }
            dag.embedding.insert(t.clone(), node.clone());
            return node;
        }
    }
}

fn ground_instances(dag: &KBEGraph) -> Vec<Term> {
    // term instance and subterm
    fn aux(node: Node) -> (Term, Vec<Term>) {
        let subs: Vec<(Term, Vec<Term>)> = node
            .children_ref()
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
            node.label(),
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
        Term::Variable(var) => node.label() == var.0,
        Term::Function(f, ts) => {
            if node.label() != f.clone() {
                return false;
            }
            if node.children_ref().len() != ts.len() {
                return false;
            }
            for (child, t_prime) in node.children_ref().iter().zip(ts.iter()) {
                if !node_match_term(child, t_prime) {
                    return false;
                }
            }
            true
        }
    }
}

fn simplify_dag_with_rule(dag: &mut KBEGraph, rule: &Rule) -> () {
    fn aux(node: &Node, dag: &mut KBEGraph, rule: &Rule) -> () { 
        // top up
        if node_match_term(node, &rule.0) {
            // apply rule
            // (rule destination is already simplified by KBO)
            let new_node = embed(&rule.1, dag);
            // only update if not root
            if let Some((i, parent)) = dag.parent.get(node) {
                // update parent
                parent.content.borrow_mut().children[*i] = new_node.clone();
                dag.parent.insert(new_node, (*i, parent.clone()));
            }
            // old children have to be preserved (thus becoming roots)
            for child in node.children_ref().iter() {
                dag.roots.insert(child.clone());
                dag.parent.remove(child);
            }
            // visit all new roots recursively (that is the default -> drop down to else)
        }
        for child in node.children_ref().iter() {
            aux(child, dag, rule);
        }
    }
    // let mut visit_roots = dag.roots.iter().cloned().collect::<Vec<Node>>();
    // while !visit_roots.is_empty() {
    //     let node = visit_roots.pop().unwrap();
    //     let new_roots = aux(&node, dag, rule);
    //     visit_roots.extend(new_roots);
    // }

    let orig_roots = dag.roots.clone();
    for root in orig_roots.iter() {
        aux(root, dag, rule);
    }
}

// expect grounded rules
fn simplify_dag(dag: &mut KBEGraph, rules: &RuleSet) -> () {
    for rule in rules.iter() {
        simplify_dag_with_rule(dag, rule);
    }
}

fn main() {

    // println!("{}","Hello" == "Hello");
    // println!("{}",&"Hello".to_string() == &"Hello".to_string());
    // let b = "Hell".to_string();
    // let b2 = b+"o";
    // println!("{}",&"Hello".to_string() == &b2);
    // panic!();

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
    let t = parseterm("M(I(M(b,M(a, M(I(a), I(b))))),c)"); // -> z

    // Step 0
    let lpo = |t: &Term, t_prime: &Term| lpo_gt(&pre, t, t_prime);
    // we changed (by init) our R/E, so KBO
    let state = knuth_loop(true, &lpo, (rules, eqs));
    rules = state.0;
    eqs = state.1;

    let t_prime = linorm(&rules, &t);
    println!("Rules:");
    printrules(&rules);
    println!("Equations:");
    printeqs(&eqs);
    println!("Result:");
    println!("{}", strterm(&t_prime));

    // Step 1
    // TODO: map/ ast graph
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
        nodecount: 0,
        embedding: HashMap::new(),
        roots: HashSet::new(),
        parent: HashMap::new(),
    };

    // Note: our graph is grounded, our rules not necessarily
    let t_node = embed(&t, &mut dag);
    dag.roots.insert(t_node.clone());

    // Step 2
    // we have init R, E in Step 0

    // Step 3
    for i in 0..5 {
        println!();
        println!();
        println!("Iteration {}", i);
        // Step 3.1 (e-graph phase)
        // TODO: match using rules (can they ever apply?)/equations (as rules both sides), add ground equations (oriented to R)
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
        // for t in ground_instances.iter() {
        //     println!("  {}", strterm(t));
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

        // TODO: only add some critical pairs (ematch or grounded)
        eqs.extend(cps);
        let state = knuth_loop(true, &lpo, (rules, eqs));
        rules = state.0;
        eqs = state.1;
        println!("Rules:");
        printrules(&rules);
        println!("Equations:");
        printeqs(&eqs);

        println!("Result:");
        let t_prime = linorm(&rules, &t);
        println!("{}", strterm(&t_prime));
    }
}
