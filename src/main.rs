mod trs;

// fn main() {
//     println!("Hello, world!");
// }

// Completion procedures based on Knuth–Bendix – a Rust translation.
//
// Many helper functions (such as `nodes`, `vars`, `subst`, `linorm`, 
// `contain`, `decvarsub`, `distincteqs`, `printeqs`, `printrules`, and so on)
// as well as the types `Term`, `Rule`, `Equation`, etc., are assumed to be declared 
// (see the provided type definitions).

use std::cmp;
use std::fmt;
use std::error::Error;

use trs::call;
use trs::parseeqs;
use trs::printrule;
use trs::strterm;
use trs::uniquevar;
use trs::var;

use crate::trs::{
    decvarsub, distincteqs, linorm, nodes, printeqs, printrules, subst, vars, contain,
    Equation, EquationSet, FunSym, Rule, RuleSet, Substitution, SubstitutionSet, Term, VarSym,
    Precedence,
};

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
                    new_subst.extend(
                        subst_var
                            .iter()
                            .map(|(x, a)| (x.clone(), subst(&vec![(var.clone(), t_prime.clone())], a))),
                    );
                    Some(new_subst)
                }
            }
        }
        Term::Function(f, ts) => {
            match t_prime {
                Term::Variable(var_prime) => {
                    if vars(t).contains(var_prime) {
                        None
                    } else {
                        let mut new_subst = vec![(var_prime.clone(), t.clone())];
                        new_subst.extend(
                            subst_var
                                .iter()
                                .map(|(x, a)| (x.clone(), subst(&vec![(var_prime.clone(), t.clone())], a))),
                        );
                        Some(new_subst)
                    }
                }
                Term::Function(f_prime, ts_prime) if f == f_prime => {
                    unify_term_lists(subst_var.clone(), ts, ts_prime)
                }
                _ => None,
            }
        }
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
    let new_terms1: Vec<Term> = terms1[1..]
        .iter()
        .map(|t| subst(&new_subst, t))
        .collect();
    let new_terms2: Vec<Term> = terms2[1..]
        .iter()
        .map(|t| subst(&new_subst, t))
        .collect();
    unify_term_lists(new_subst, &new_terms1, &new_terms2)
}

/// A convenience function to unify two terms starting with an empty substitution.
/// (The resulting substitution is “reversed” as in the OCaml version.)
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
fn critical_pair_parts_list(
    ts: &[Term],
    rule: &Rule,
) -> Vec<(Vec<Term>, SubstitutionSet)> {
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
        if !result.iter().any(|(a, b)| (a == y && b == x) || (a == x && b == y)) {
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
            let option2 = symbol_greater(pre, f, f_prime)
                && ts_prime.iter().all(|tpp| lpo_gt(pre, t, tpp));
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

/// Selects the rule with lower complexity.
// fn choose_rule<'a>(r1: &'a Rule, r2: &'a Rule) -> &'a Rule {
//     if rule_complexity(r1) > rule_complexity(r2) {
//         r2
//     } else {
//         r1
//     }
// }

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
fn deduce_critical_pairs((r, rules, eqs): (Rule, RuleSet, EquationSet)) -> (Rule, RuleSet, EquationSet) {
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
    print!("oriented: ");
    printrule(&oriented.0);
    let composed = compose(oriented);
    let deduced = deduce_critical_pairs(composed);
    println!("deduced equations: ");
    printeqs(&deduced.2);
    let collapsed = collapse(deduced);
    let added = add_rule(collapsed);
    println!("rules after adding: ");
    printrules(&added.0);
    let simplified = simplify(added);
    println!("simplified equations: ");
    printeqs(&simplified.1);
    println!("simplified rules: ");
    printrules(&simplified.0);

    let t = call("M", vec![call("I", vec![var("x_1")]), call("M", vec![var("x_1"), var("z")])]);
    let rules = &simplified.0;
    let t_norm = linorm(&rules, &t);
    println!("M(I(x1),M(x1,z)) -> {}", strterm(&t_norm));

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

//
// Helper stubs
//
// The following functions are assumed to exist. In a complete system they would be implemented
// or imported from appropriate modules.
/// Renames the variables in the given rules apart.
// fn uniquevar(rule1: &Rule, rule2: &Rule) -> (Rule, Rule) {
//     // Stub: in a complete implementation, return rules with renamed variables.
//     (rule1.clone(), rule2.clone())
// }

fn main() {
    // println!("Hello, world!");

    let pre: Precedence = vec![
        // (FunSym("I".to_string()), 3),
        // (FunSym("M".to_string()), 2),
        // (FunSym("E".to_string()), 1),
        (String::from("I"), 3),
        (String::from("M"), 2),
        (String::from("E"), 1),
    ];
    let eqs : EquationSet = parseeqs(vec![
        "M(M(x,y),z)=M(x,M(y,z))", 
        "M(I(x),x)=E", 
        "M(E,x)=x"
    ]);
    knuth_bendix_completion_verbose_precedence(&pre, eqs);

}
