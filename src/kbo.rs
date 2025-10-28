use std::cmp;
use std::error::Error;
use std::fmt;
use std::collections::HashMap;
use std::sync::Mutex;
use std::thread::panicking;
use either::Either;
use once_cell::sync::Lazy;
// use std::cell::RefCell;
// use std::collections::HashSet as StdHashSet;


use term_rewrite::uniquevar;

use crate::term_rewrite;
use crate::term_rewrite::*;
use crate::types::*;
use crate::util::is_constant;

/// Simple memoization cache for LPO computations
static LPO_CACHE: Lazy<Mutex<HashMap<(Term, Term), bool>>> = Lazy::new(|| Mutex::new(HashMap::new()));

// thread_local! {
//     static KBO_IN_PROGRESS: RefCell<StdHashSet<(Term, Term)>> = RefCell::new(StdHashSet::new());
// }

/// Clears the LPO cache to free memory
// pub fn clear_lpo_cache() {
//     if let Ok(mut cache) = LPO_CACHE.lock() {
//         cache.clear();
//     }
// }

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
pub fn critical_pair(rule1: &Rule, rule2: &Rule) -> Vec<(Term, Term)> {
    // Assume that `uniquevar` takes a pair of rules and returns a pair with variables renamed apart.
    let (rule1_prime, rule2_prime) = uniquevar(rule1, rule2);
    let (l1, r1) = &rule1_prime;
    let (l2, r2) = &rule2_prime;
    let mut pairs = Vec::new();
    pairs.extend(apply_cp_subst(r1, critical_pair_parts(l1, &rule2_prime)));
    pairs.extend(apply_cp_subst(r2, critical_pair_parts(l2, &rule1_prime)));
    remove_symmetric_duplicates(pairs)
}

pub fn critical_pair_ref(rule1: (&Term, &Term), rule2: (&Term,&Term)) -> Vec<(Term, Term)> {
    // Assume that `uniquevar` takes a pair of rules and returns a pair with variables renamed apart.
    let (rule1_prime, rule2_prime) = uniquevar_ref(rule1, rule2);
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
    let i_pos = i.unwrap_or(0);
    let j_pos = j.unwrap_or(0);
    i_pos > j_pos
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
        for (x, y) in xs.iter().zip(ys.iter()) {
            if strictly_greater(greq, x, y) {
                return true;
            } else if equivalent_by_order(greq, x, y) {
                continue;
            } else {
                return false;
            }
        }
        return xs.len() >= ys.len();
        // let x = &xs[0];
        // let y = &ys[0];
        // if strictly_greater(greq, x, y) {
        //     true
        // } else if equivalent_by_order(greq, x, y) {
        //     lexicographic_greq(greq, &xs[1..], &ys[1..])
        // } else {
        //     false
        // }
    }
}

fn lexicographic_kbo<F>(kbo: &F, xs: &[Term], ys: &[Term]) -> bool
where
    F: Fn(&Term, &Term) -> bool,
{
    if xs.is_empty() {
        false // nothing is not greater than nothing (and also not greater than anything)
    } else if ys.is_empty() {
        true
    } else {
        for (x, y) in xs.iter().zip(ys.iter()) {
            // If the current head elements are syntactically equal, skip them and
            // continue with the remaining tails. This avoids re-invoking the
            // comparator on identical subterms, which can create recursion cycles.
            if x == y {
                continue;
            }
            if kbo(x, y) {
                return true;
            }
            if kbo(y, x) {
                return false;
            }
        }
        return xs.len() > ys.len();

        // let x = &xs[0];
        // let y = &ys[0];
        // // If the current head elements are syntactically equal, skip them and
        // // continue with the remaining tails. This avoids re-invoking the
        // // comparator on identical subterms, which can create recursion cycles.
        // if x == y {
        //     return lexicographic_kbo(kbo, &xs[1..], &ys[1..]);
        // }
        // if kbo(x, y) { // x > y
        //     true
        // } else if kbo(y, x) { // y > x
        //     false
        // } else { // x not greater or smaller than y
        //     lexicographic_kbo(kbo, &xs[1..], &ys[1..])
        // }
    }
}

// we use ? for variable weight
// restrictions: variable all same, smaller (or equal to all constants)
// if one unary symbol has weight 0, it needs to be the largest symbol
fn weight(w: &Weight, t: &Term, count: &mut HashMap<VarSym, i32>, increment: bool) -> usize {
    match t {
        Term::Variable(v) => {
            count.insert(v.clone(), count.get(&v).map(|c| *c).unwrap_or(0) + if increment { 1 } else { -1 });
            w.iter().find(|(sym, _)| sym == &"?".into()).map(|(_, w)| *w).unwrap_or(0)},
        Term::Function(f, ts) => 
            // if f.to_string().to_lowercase() == "if" {
            //     // if(cond, simplified, originalterm) => just take weight of simplified
            //     println!("If: {}", strterm(t));
            //     println!("If: {:?}", ts);
            //     println!("If then: {}", strterm(&ts[1]));
            //     println!();
            //     weight(w, &ts[1], count, increment)
            // } else 
            if is_constant(f).is_some() {
                1
            } else {
                w.iter()
                    .find(|(sym, _)| sym == f)
                    .map(|(_, w)| *w).unwrap_or(2) + 
                // 2 +
                ts.iter().map(|t| weight(w, t, count, increment)).sum::<usize>()
            }
    }
}

// for cp weight (not used in kbo itself -- see weight function)
// variable 0, function symbols 1
pub fn term_weight(w: &Weight, t: &Term) -> usize {
    match t {
        Term::Variable(_) => {
            w.iter().find(|(sym, _)| sym == &"?".into()).map(|(_, w)| *w).unwrap_or(0)
            // 0
        },
        Term::Function(f, ts) => 
            // if f.to_string().to_lowercase() == "if" {
            //     // if(cond, simplified, originalterm) => just take weight of simplified
            //     term_weight(w, &ts[1])
            // } else 
            if is_constant(f).is_some() {
                1
            } else {
                w.iter()
                    .find(|(sym, _)| sym == f)
                    .map(|(_, w)| *w).unwrap_or(2) + 
                ts.iter().map(|t| term_weight(w, t)).sum::<usize>()
            }
    }
}

fn is_unary_wrap(t:&Term, x: &VarSym, symbol: Option<&FunSym>) -> bool {
    match t {
        Term::Variable(v) => v == x,
        Term::Function(f, ts) => ts.len() == 1 && is_unary_wrap(&ts[0], x, Some(f)) && (symbol.is_none() || symbol.unwrap() == f)
    }
}

/// The lexicographic path ordering (LPO) “greater–or–equal” relation with respect to `pre`.
/// TODO: too expensive to compute
pub fn kbo_gt(pre: &Precedence, w: &Weight, t: &Term, t_prime: &Term) -> bool {
    // Check cache first
    let key = (t.clone(), t_prime.clone());
    if let Ok(cache) = LPO_CACHE.lock() {
        if let Some(&result) = cache.get(&key) {
            return result;
        }
    }

    // Detect direct or mutual recursion on the same pair and short-circuit
    // let already_in_progress = KBO_IN_PROGRESS.with(|set| {
    //     let mut set_b = set.borrow_mut();
    //     if set_b.contains(&key) {
    //         true
    //     } else {
    //         set_b.insert(key.clone());
    //         false
    //     }
    // });
    // if already_in_progress {
    //     return false;
    // }

    // if t == t_prime {
    //     return false;
    // }

    let mut var_count = HashMap::new();
    let wt = weight(w, t, &mut var_count, true);
    let wt_prime = weight(w, t_prime, &mut var_count, false);
    let mut _all_neg = true; // all vars <= 0, t_prime has more or same as t
    let mut all_pos = true; // all vars >= 0, in t same or more than t_prime
    for (_, count) in var_count.iter() {
        if *count > 0 {
            _all_neg = false;
        }
        if *count < 0 {
            all_pos = false;
        }
    }
    let result = {
        if !all_pos {
            false
        } else if wt > wt_prime {
            true
        } else 
        // if all_neg && wt < wt_prime {
        //     return false; // we do not just know !(t > t_prime) but we even know t_prime > t
        // }
        if wt < wt_prime {
            // at least can not be greater
            false
        } else {

        // we know w(t) = w(t')
        
        // Compute the result
        match (t, t_prime) {
            // t = f^n(x), t' = x
            // we know the variable is a subterm => contained (by variable count)
            (Term::Function(_, _), Term::Variable(_)) => true,
            // (Term::Function(_, _), Term::Variable(x)) => is_unary_wrap(t, x, None),
            (Term::Function(f, ts), Term::Function(g, ts_prime)) => {
                if f == g {
                    // t = f(t1, ..., tn), t' = g(t1', ..., tn'), (t1, ..., tn) >lex (t1', ..., tn')
                    lexicographic_kbo(&|a, b| kbo_gt(pre, w, a, b), ts, ts_prime)
                } else {
                    // t = f(...), t' = g(...), f > g
                    let pt = pre.iter().find(|(sym, _)| sym == f).map(|(_, p)| *p);
                    let pt_prime = pre.iter().find(|(sym, _)| sym == g).map(|(_, p)| *p);
                    // num lands in the or case
                    let pt_pos = pt.unwrap_or(0);
                    let pt_prime_pos = pt_prime.unwrap_or(0);
                    pt_pos > pt_prime_pos
                    // TODO: need to check t > all elements of list
                }
            },
            _ => false,
    //         (_, Term::Variable(var_prime)) => vars(t).contains(var_prime),
    //         (Term::Variable(_), _) => false,
    //         (Term::Function(f, ts), Term::Function(f_prime, ts_prime)) => {
    //             (
    //             symbol_equal(pre, f, f_prime)
    //                 && lexicographic_greq(&|a, b| lpo_ge(pre, weight, a, b), ts, ts_prime)
    //                 && ts_prime.iter().all(|tpp| lpo_gt(pre, weight, t, tpp))
    //             ) || 
    //             (
    // symbol_greater(pre, f, f_prime) && ts_prime.iter().all(|tpp| lpo_gt(pre, weight, t, tpp))
    //             ) || 
    //             (
    //                 ts.iter().any(|tpp| lpo_ge(pre, weight, tpp, t_prime))
    //             )


    //             // let option1 = symbol_equal(pre, f, f_prime)
    //             //     && lexicographic_greq(&|a, b| lpo_ge(pre, a, b), ts, ts_prime)
    //             //     && ts_prime.iter().all(|tpp| lpo_gt(pre, t, tpp));
    //             // let option2 =
    //             //     symbol_greater(pre, f, f_prime) && ts_prime.iter().all(|tpp| lpo_gt(pre, t, tpp));
    //             // let option3 = ts.iter().any(|tpp| lpo_ge(pre, tpp, t_prime));
    //             // option1 || option2 || option3
    //         }
        }
        }
    };
    
    // Store result in cache
    if let Ok(mut cache) = LPO_CACHE.lock() {
        cache.insert(key, result);
    }
    // KBO_IN_PROGRESS.with(|set| { set.borrow_mut().remove(&(t.clone(), t_prime.clone())); });
    
    result
}

/// The strict part of `lpo_ge`.
// pub fn lpo_gt(pre: &Precedence, weight: &Weight, t: &Term, t_prime: &Term) -> bool {
//     lpo_ge(pre, weight, t, t_prime) && !lpo_ge(pre, weight, t_prime, t)
// }


// fn kbo_ge(pre: &Precedence, t: &Term, t_prime: &Term) -> bool {
// }

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
pub fn orient_equation<F>(
    lpo: &F,
    state: (StagedVec<Rule>, StagedVec<Equation>),
) -> Either<(Rule, StagedVec<Rule>, StagedVec<Equation>), (StagedVec<Rule>, StagedVec<Equation>)>
// Result<(Rule, RuleSet, EquationSet), CompletionFailed>
where
    F: Fn(&Term, &Term) -> bool,
{
    // eqs.current were already tried and are unorientable
    let (rules, eqs) = state;
    let orientable: Vec<Equation> = eqs.staged
        .iter()
        .filter(|(l, r)| lpo(l, r) || lpo(r, l))
        .cloned()
        .collect();
    if orientable.is_empty() {
        // println!("No orientable equations in state");
        // printeqs(&eqs.staged);
        // for (l, r) in eqs.staged.iter() {
        //     println!("Equation: {:?} = {:?}", l, r);
        //     println!("LPO {} vs {}: {}", strterm(l), strterm(r), lpo(l, r));
        //     println!("LPO {} vs {}: {}", strterm(r), strterm(l), lpo(r, l));
        //     println!();
        // }
        // panic!();
        // return Err(CompletionFailed);
        return Either::Right((rules, eqs));
    }
    // TODO: orient all?
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
    let new_eqs: EquationSet = eqs.staged.into_iter().filter(|e| *e != chosen).collect();
    // Ok((new_rule, rules, new_eqs))
    Either::Left((new_rule, rules, StagedVec::rebuild(eqs.current, new_eqs)))
}

/// Normalizes the right–hand sides of `rules` using the new rule `r`.
pub fn compose((r, rules, eqs): (Rule, StagedVec<Rule>, StagedVec<Equation>)) -> (Rule, StagedVec<Rule>, StagedVec<Equation>) {
    let mut r_and_rules = vec![&r];
    r_and_rules.extend(rules.current.iter());
    r_and_rules.extend(rules.staged.iter());
    let new_rules_current: RuleSet = rules.current
        .iter()
        .map(|(l, r_prime)| (l.clone(), linorm_ref(&r_and_rules, &r_prime)))
        .collect();
    let new_rules_staged: RuleSet = rules.staged
        .iter()
        .map(|(l, r_prime)| (l.clone(), linorm_ref(&r_and_rules, &r_prime)))
        .collect();
    (r, StagedVec::rebuild(new_rules_current, new_rules_staged), eqs)
}

/// Adds all critical pairs deducible from `r` (with each rule in `r :: rules`)
/// to the set of equations.
pub fn deduce_critical_pairs(
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
// TODO: this is wrong compared to "real" KBO
// pub fn collapse<F>(lpo_gt: &F, (rule, rules, eqs): (Rule, RuleSet, EquationSet)) -> (Rule, RuleSet, EquationSet) 
// where
//     F: Fn(&Term, &Term) -> bool,
// {
//     let (l, _) = &rule;
//     // collapse with other rules
//     // Part1: simplify other rules with this one
//     // if others left side is larger than other, add new as equation

//     // let to_simplify = rules.into_iter()
//     //     .filter(|(l_prime, _)| lpo_gt(l_prime, l))
//     //     .collect::<RuleSet>();
//     let (to_simplify, remaining) = rules.into_iter()
//         .partition::<RuleSet, _>(|(l_prime, _)| lpo_gt(l_prime, l));

//     // simplify the left side with the rule
//     for (l_prime, r_prime) in to_simplify {
//         let new_left = linorm(&[l.clone()], &l_prime);
//         let new_right = linorm(&[l.clone()], &r_prime);
//         eqs.insert((new_left, new_right));
//     }


//     (rule, new_rules, eqs)
// }

/// Adds the new rule `r` to the set of rules.
pub fn add_rule((r, rules, eqs): (Rule, StagedVec<Rule>, StagedVec<Equation>)) -> (StagedVec<Rule>, StagedVec<Equation>) {
    let mut new_rules = rules;
    // Avoid inserting duplicate rules (modulo variable renaming)
    // let already_present = new_rules.iter().any(|existing| sameeq(existing, &r));
    // if !already_present {
        new_rules.staged.insert(0, r);
    // }
    (new_rules, eqs)
}

/// Normalizes both sides of every equation in `eqs` using the current rules.
pub fn simplify((rules, eqs): (StagedVec<Rule>, StagedVec<Equation>)) -> (StagedVec<Rule>, StagedVec<Equation>) {
    let all_rules = rules.iter_all().collect::<Vec<_>>();
    let new_eqs_staged: EquationSet = eqs.staged
        .into_iter()
        .map(|(l, r)| (linorm_ref(&all_rules, &l), linorm_ref(&all_rules, &r)))
        .collect();
    // TODO: do we need to normalize old equations?
    let new_eqs_current: EquationSet = eqs.current
        .into_iter()
        .map(|(l, r)| (linorm_ref(&all_rules, &l), linorm_ref(&all_rules, &r)))
        .collect();
    (rules, StagedVec::rebuild(new_eqs_current,new_eqs_staged))
}

/// Removes trivial equations (where both sides are equal). If `verbose` is true,
/// duplicate equations are also removed via `distincteqs`.
pub fn remove_trivial(verbose: bool, (rules, eqs): (StagedVec<Rule>, StagedVec<Equation>)) -> (StagedVec<Rule>, StagedVec<Equation>) {
    // let eqs = if verbose { distincteqs(eqs) } else { eqs };
    // let new_eqs: EquationSet = eqs.into_iter().filter(|(l, r)| l != r).collect();
    let new_eqs_staged: EquationSet = eqs.staged.into_iter().filter(|(l, r)| l != r).collect();
    // TODO: current should probably already be simplified
    let new_eqs_current: EquationSet = eqs.current.into_iter().filter(|(l, r)| l != r).collect();
    (rules, StagedVec::rebuild(new_eqs_current,new_eqs_staged))
}

/// Performs one Knuth–Bendix completion step on the current state using ordering `lpo`.
// fn completion_step<F>(
//     verbose: bool,
//     lpo: &F,
//     state: (RuleSet, EquationSet),
// ) -> (RuleSet, EquationSet)
// where
//     F: Fn(&Term, &Term) -> bool,
// {
//     let oriented = orient_equation(lpo, state).left().unwrap();
//     let composed = compose(oriented);
//     let deduced = deduce_critical_pairs(composed);
//     // let collapsed = collapse(lpo,deduced);
//     let collapsed = deduced;
//     let added = add_rule(collapsed);
//     let simplified = simplify(added);
//     let removed = remove_trivial(verbose, simplified);
//     removed
// }

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
// fn completion_loop<F>(
//     verbose: bool,
//     mut n: usize,
//     lpo: &F,
//     mut state: (RuleSet, EquationSet),
// ) -> RuleSet
// where
//     F: Fn(&Term, &Term) -> bool,
// {
//     if n == 0 {
//         if verbose {
//             print_input(&state.1);
//         }
//         state = completion_step(verbose, lpo, state);
//         n = 1;
//     }
//     loop {
//         let (ref rules, ref eqs) = state;
//         if eqs.is_empty() {
//             let rules_prime: RuleSet = rules.iter().map(|r| decvarsub(r)).collect();
//             if verbose {
//                 print_output(n, &rules_prime);
//             }
//             return rules_prime;
//         } else {
//             if verbose {
//                 print_step(n, rules, eqs);
//             }
//             state = completion_step(verbose, lpo, state);
//             n += 1;
//         }
//     }
// }

// /// Runs the Knuth–Bendix completion algorithm with ordering `lpo` and initial equations `eqs`.
// pub fn knuth_bendix_completion<F>(lpo: &F, eqs: EquationSet) -> RuleSet
// where
//     F: Fn(&Term, &Term) -> bool,
// {
//     let initial_state = remove_trivial(false, (vec![], eqs));
//     completion_loop(false, 0, lpo, initial_state)
// }

// /// Runs completion using the ordering induced by the precedence `pre`.
// pub fn knuth_bendix_completion_precedence(pre: &Precedence, eqs: EquationSet) -> RuleSet {
//     knuth_bendix_completion(&|t, t_prime| lpo_gt(pre, t, t_prime), eqs)
// }

// /// Runs the Knuth–Bendix completion algorithm with verbose output.
// pub fn knuth_bendix_completion_verbose<F>(lpo: &F, eqs: EquationSet) -> RuleSet
// where
//     F: Fn(&Term, &Term) -> bool,
// {
//     let initial_state = remove_trivial(false, (vec![], eqs));
//     completion_loop(true, 0, lpo, initial_state)
// }

// /// Runs the verbose completion version with an ordering induced by `pre`.
// pub fn knuth_bendix_completion_verbose_precedence(pre: &Precedence, eqs: EquationSet) -> RuleSet {
//     knuth_bendix_completion_verbose(&|t, t_prime| lpo_gt(pre, t, t_prime), eqs)
// }

pub fn term_size(pre: &Precedence, t: &Term) -> usize 
{
    match t {
        Term::Variable(_) => 1,
        Term::Function(f, ts) => 
            pre.iter().find(|(f_prime, _)| f_prime == f).map(|(_, p)| *p).unwrap_or(0) as usize + 
            ts.iter().map(|t| term_size(pre, t)).sum::<usize>()
    }
}


fn lpo_ge(pre: &Precedence, t: &Term, t_prime: &Term) -> bool {
    // Check cache first
    let key = (t.clone(), t_prime.clone());
    if let Ok(cache) = LPO_CACHE.lock() {
        if let Some(&result) = cache.get(&key) {
            return result;
        }
    }
    
    // Compute the result
    let result = match (t, t_prime) {
        (_, Term::Variable(var_prime)) => vars(t).contains(var_prime),
        (Term::Variable(_), _) => false,
        (Term::Function(f, ts), Term::Function(f_prime, ts_prime)) => {
            (
            symbol_equal(pre, f, f_prime)
                && lexicographic_greq(&|a, b| lpo_ge(pre, a, b), ts, ts_prime)
                && ts_prime.iter().all(|tpp| lpo_gt(pre, t, tpp))
            ) || 
            (
symbol_greater(pre, f, f_prime) && ts_prime.iter().all(|tpp| lpo_gt(pre, t, tpp))
            ) || 
            (
                ts.iter().any(|tpp| lpo_ge(pre, tpp, t_prime))
            )


            // let option1 = symbol_equal(pre, f, f_prime)
            //     && lexicographic_greq(&|a, b| lpo_ge(pre, a, b), ts, ts_prime)
            //     && ts_prime.iter().all(|tpp| lpo_gt(pre, t, tpp));
            // let option2 =
            //     symbol_greater(pre, f, f_prime) && ts_prime.iter().all(|tpp| lpo_gt(pre, t, tpp));
            // let option3 = ts.iter().any(|tpp| lpo_ge(pre, tpp, t_prime));
            // option1 || option2 || option3

        }
    };

    // Store result in cache
    if let Ok(mut cache) = LPO_CACHE.lock() {
        cache.insert(key, result);
    }


    result
}


pub fn lpo_gt(pre: &Precedence, t: &Term, t_prime: &Term) -> bool {
    lpo_ge(pre, t, t_prime) && !lpo_ge(pre, t_prime, t)
}

