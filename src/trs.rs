use std::fmt;
use std::error::Error;

pub type FunSym = String;
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarSym(pub String, pub i32);
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Variable(VarSym),
    Function(FunSym, Vec<Term>),
}
pub type Rule = (Term, Term);
pub type Equation = (Term, Term);
pub type Substitution = (VarSym, Term);
pub type RuleSet = Vec<Rule>;
pub type EquationSet = Vec<Equation>;
pub type SubstitutionSet = Vec<Substitution>;
pub type Precedence = Vec<(FunSym, i32)>;

/// Error type to indicate that the completion process failed.
#[derive(Debug)]
pub struct CompletionFailed;

impl fmt::Display for CompletionFailed {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CompletionFailed")
    }
}

impl Error for CompletionFailed {}



//
// Helper functions on vectors
//

/// Returns the union of two vectors (without duplicates).
fn union<T: Clone + PartialEq>(mut v1: Vec<T>, v2: Vec<T>) -> Vec<T> {
    for item in v2 {
        if !v1.contains(&item) {
            v1.push(item);
        }
    }
    v1
}

/// Returns the intersection of two vectors.
fn intersection<T: Clone + PartialEq>(v1: Vec<T>, v2: Vec<T>) -> Vec<T> {
    v1.into_iter().filter(|x| v2.contains(x)).collect()
}

/// Subtracts all elements in `to_remove` from `v`.
fn subtraction<T: Clone + PartialEq>(v: Vec<T>, to_remove: Vec<T>) -> Vec<T> {
    v.into_iter().filter(|item| !to_remove.contains(item)).collect()
}

/// Finds a substitution for a variable in a substitution set.
/// only lifetime in code
fn find_substitution<'a>(xi: &'a VarSym, ss: &'a SubstitutionSet) -> Option<&'a Term> {
    for (var, term) in ss {
        if var == xi {
            return Some(term);
        }
    }
    None
}

//
// Basic term–functions
//

/// [nodes t] returns the total number of nodes in term [t].
pub fn nodes(t: &Term) -> usize {
    match t {
        Term::Variable(_) => 1,
        Term::Function(_, ts) => 1 + nodeslist(ts),
    }
}

/// [nodeslist ts] returns the sum of the nodes in a list of terms.
pub fn nodeslist(ts: &[Term]) -> usize {
    ts.iter().map(|t| nodes(t)).sum()
}

/// [vars t] returns the list of variable symbols occurring in [t].
pub fn vars(t: &Term) -> Vec<VarSym> {
    match t {
        Term::Variable(xi) => vec![xi.clone()],
        Term::Function(_, ts) => varslist(ts),
    }
}

/// [varslist ts] returns the union (without duplicates) of the variable lists of terms.
pub fn varslist(ts: &[Term]) -> Vec<VarSym> {
    ts.iter()
        .map(|t| vars(t))
        .fold(Vec::new(), |acc, v| union(acc, v))
}

/// [subst ss t] recursively applies the substitution set [ss] to term [t].
pub fn subst(ss: &SubstitutionSet, t: &Term) -> Term {
    match t {
        Term::Variable(xi) => {
            if let Some(s) = find_substitution(xi, ss) {
                s.clone()
            } else {
                t.clone()
            }
        }
        Term::Function(f, ts) => {
            let new_ts = ts.iter().map(|t| subst(ss, t)).collect();
            Term::Function(f.clone(), new_ts)
        }
    }
}

/// [collate l r] returns a substitution [ss] such that applying [ss] to [l] makes it equal to [r].
pub fn collate(l: &Term, r: &Term) -> Option<SubstitutionSet> {
    match l {
        Term::Variable(xi) => Some(vec![(xi.clone(), r.clone())]),

        Term::Function(f, ts) => match r {
            Term::Variable(_) => None,
            Term::Function(f_prime, ts_prime) => {
                if f == f_prime {
                    collatelist(ts, ts_prime)
                } else {
                    None
                }
            }
        },
    }
}

/// Attempts to extend `xs` with all substitutions in `ys`, provided that if a key
/// is already present in `xs` then its value agrees with the one in `ys`.
/// Returns `Some(extended)` if successful, or `None` if there is a conflict.
pub fn duplicate_free_extend(
    xs: &SubstitutionSet,
    ys: &SubstitutionSet,
) -> Option<SubstitutionSet> {
    if ys.is_empty() {
        return Some(xs.clone());
    }
    let (k, v) = &ys[0];

    // Check whether xs already contains a substitution for k.
    if let Some((_, x)) = xs.iter().find(|(key, _)| key == k) {
        if x == v {
            duplicate_free_extend(xs, &ys[1..].to_vec())
        } else {
            None
        }
    } else {
        if let Some(mut zs) = duplicate_free_extend(xs, &ys[1..].to_vec()) {
            zs.insert(0, (k.clone(), v.clone()));
            Some(zs)
        } else {
            None
        }
    }
}


/// [collatelist ls rs] returns a substitution if every corresponding pair in [ls] and [rs] collates.
pub fn collatelist(ls: &[Term], rs: &[Term]) -> Option<SubstitutionSet> {
    if ls.len() != rs.len() {
        return None;
    }
    let mut result = Vec::new();
    for (t, t_prime) in ls.iter().zip(rs.iter()) {
        if let Some(s) = collate(t, t_prime) {
            // result.extend(s);
            result = match duplicate_free_extend(&result, &s) {
                Some(sub) => sub,
                None => return None,
            };
        } else {
            return None;
        }
    }
    Some(result)
}

/// [contain l r] returns true if [l] occurs in [r] (by means of a successful collate).
pub fn contain(l: &Term, r: &Term) -> bool {
    match r {
        Term::Variable(_) => collate(l, r).is_some(),
        Term::Function(_, ts) => collate(l, r).is_some() || containlist(l, ts),
    }
}

/// [containlist l ts] checks whether [l] occurs in any term of [ts].
pub fn containlist(l: &Term, ts: &[Term]) -> bool {
    ts.iter().any(|t| contain(l, t))
}

//
// Reduction functions (left‐to‐right, outermost, etc.)
//

/// [linormtop rs sub_rs t] normalizes [t] by scanning the rule list [sub_rs] (which is
/// normally the entire rewrite set [rs]). If no rule applies, [t] is returned unchanged.
pub fn linormtop(rs: &RuleSet, sub_rs: &[Rule], t: &Term) -> Term {
    if sub_rs.is_empty() {
        t.clone()
    } else {
        let (l, r) = &sub_rs[0];
        if let Some(s) = collate(l, t) {
            linormsubst(rs, &s, r)
        } else {
            linormtop(rs, &sub_rs[1..], t)
        }
    }
}

/// [linormsubst rs s t] applies the substitution [s] to [t] and then normalizes.
pub fn linormsubst(rs: &RuleSet, s: &SubstitutionSet, t: &Term) -> Term {
    match t {
        Term::Variable(_) => subst(s, t),
        Term::Function(f, ts) => {
            let mapped = ts.iter().map(|t| linormsubst(rs, s, t)).collect();
            let new_term = Term::Function(f.clone(), mapped);
            linormtop(rs, rs, &new_term)
        }
    }
}


/// [linorm rs t] normalizes [t] with respect to [rs].
pub fn linorm(rs: &RuleSet, t: &Term) -> Term {
    match t {
        Term::Variable(_) => linormtop(rs, rs, t),
        Term::Function(f, ts) => {
            let new_ts = ts.iter().map(|t| linorm(rs, t)).collect();
            linormtop(rs, rs, &Term::Function(f.clone(), new_ts))
        }
    }
}

//
// Renaming and variable “uniquification” functions
//

/// [rename (old, new) t] replaces all occurrences of the variable [old] with [new] in [t].
pub fn rename(r: &(VarSym, VarSym), t: &Term) -> Term {
    match t {
        Term::Variable(x) if x == &r.0 => Term::Variable(r.1.clone()),
        Term::Variable(_) => t.clone(),
        Term::Function(f, ts) => Term::Function(f.clone(), renamelist(r, ts)),
    }
}

/// Applies [rename] to each term in the list.
pub fn renamelist(r: &(VarSym, VarSym), ts: &[Term]) -> Vec<Term> {
    ts.iter().map(|t| rename(r, t)).collect()
}

/// [uniquevarstep xis x_i n ru] looks for a fresh variant for [x_i] (of the form (x, n))
/// that is not yet in [xis] and renames [ru] accordingly. It returns the new rule and an updated list.
pub fn uniquevarstep(
    xis: &Vec<VarSym>,
    x_i: &VarSym,
    n: i32,
    ru: &Rule,
) -> (Rule, Vec<VarSym>) {
    let candidate = VarSym(x_i.0.clone(), n);
    if xis.contains(&candidate) {
        uniquevarstep(xis, x_i, n + 1, ru)
    } else {
        let (l, r) = ru;
        let new_l = rename(&(x_i.clone(), candidate.clone()), l);
        let new_r = rename(&(x_i.clone(), candidate.clone()), r);
        let new_rule = (new_l, new_r);
        let mut new_xis = xis.clone();
        new_xis.push(candidate);
        new_xis = subtraction(new_xis, vec![x_i.clone()]);
        (new_rule, new_xis)
    }
}

/// [uniquevarsub xis ins ru] renames all variables in [ins] (that occur in [ru]) so that
/// they are distinct from those in [xis].
pub fn uniquevarsub(mut xis: Vec<VarSym>, ins: Vec<VarSym>, ru: Rule) -> Rule {
    let mut rule_current = ru;
    for xi in ins {
        let (new_rule, new_xis) = uniquevarstep(&xis, &xi, 0, &rule_current);
        rule_current = new_rule;
        xis = new_xis;
    }
    rule_current
}

/// [uniquevar ru ru'] renames variables in the second rule [ru'] so that its variables
/// do not clash with those in the first rule [ru].
pub fn uniquevar(ru: &Rule, ru_prime: &Rule) -> (Rule, Rule) {
    let (l, r) = ru;
    let (l_prime, r_prime) = ru_prime;
    let uni = union(vars(l), vars(r));
    let ins = intersection(uni.clone(), union(vars(l_prime), vars(r_prime)));
    let new_ru_prime = uniquevarsub(uni, ins, ru_prime.clone());
    (ru.clone(), new_ru_prime)
}

/// [decvarsubstep uni x_i n ru] attempts to “de‐generalize” a variable’s index.
/// It uses the sign of the original index to choose the next candidate.
pub fn decvarsubstep(
    uni: &Vec<VarSym>,
    x_i: &VarSym,
    n: i32,
    ru: &Rule,
) -> (Rule, Vec<VarSym>) {
    let sgn = if x_i.1 >= 0 { 1 } else { -1 };
    let candidate = VarSym(x_i.0.clone(), n);
    if uni.contains(&candidate) {
        decvarsubstep(uni, x_i, n + sgn, ru)
    } else if n.abs() < x_i.1.abs() {
        let new_rule = (
            rename(&(x_i.clone(), candidate.clone()), &ru.0),
            rename(&(x_i.clone(), candidate.clone()), &ru.1),
        );
        let mut new_uni = uni.clone();
        new_uni.push(candidate);
        new_uni = subtraction(new_uni, vec![x_i.clone()]);
        (new_rule, new_uni)
    } else {
        (ru.clone(), uni.clone())
    }
}

/// [decvarsubsub uni xis ru] “de‐generalizes” variables in [xis] with respect to [ru].
pub fn decvarsubsub(mut uni: Vec<VarSym>, xis: Vec<VarSym>, ru: Rule) -> Rule {
    let mut rule_current = ru;
    for xi in xis {
        let (new_rule, new_uni) = decvarsubstep(&uni, &xi, 0, &rule_current);
        rule_current = new_rule;
        uni = new_uni;
    }
    rule_current
}

/// [decvarsub ru] applies variable de‐substitution to [ru].
pub fn decvarsub(ru: &Rule) -> Rule {
    let (l, r) = ru;
    let uni = union(vars(l), vars(r));
    let xis: Vec<VarSym> = uni.iter().cloned().filter(|v| v.1 != 0).collect();
    decvarsubsub(uni, xis, ru.clone())
}

/// [sameeq eq1 eq2] returns true if the two equations are “the same” modulo variable renaming.
pub fn sameeq(eq1: &Equation, eq2: &Equation) -> bool {
    let (l, r) = eq1;
    let (l_prime, r_prime) = eq2;
    (collate(l, l_prime).is_some()
        && collate(r, r_prime).is_some()
        && collate(l_prime, l).is_some()
        && collate(r_prime, r).is_some())
        ||
    (collate(l, r_prime).is_some()
        && collate(r, l_prime).is_some()
        && collate(r_prime, l).is_some()
        && collate(l_prime, r).is_some())
}

/// [distincteqs eqs] returns a list of equations with duplicate (i.e. equivalent)
/// equations removed.
pub fn distincteqs(eqs: Vec<Equation>) -> Vec<Equation> {
    let mut result = Vec::new();
    for eq in eqs.into_iter() {
        if !result.iter().any(|existing| sameeq(existing, &eq)) {
            result.push(eq);
        }
    }
    result
}

//
// Constructors for terms
//

/// [var x] creates a variable named [x] with index 0.
pub fn var(x: &str) -> Term {
    Term::Variable(VarSym(x.to_string(), 0))
}

/// [const_ c] creates a constant (a function symbol with no arguments).
pub fn const_(c: &str) -> Term {
    Term::Function(c.to_string(), vec![])
}

/// [func f xs] creates a function application whose arguments are the variables named in [xs].
pub fn func(f: &str, xs: &[&str]) -> Term {
    let vars: Vec<Term> = xs.iter().map(|x| var(x)).collect();
    Term::Function(f.to_string(), vars)
}

/// [call f ts] creates a function application with the given list of terms.
pub fn call(f: &str, ts: Vec<Term>) -> Term {
    Term::Function(f.to_string(), ts)
}

/// [nest f n t] nests the term [t] under [n] occurrences of the function symbol [f].
pub fn nest(f: &str, n: usize, t: Term) -> Term {
    if n > 0 {
        Term::Function(f.to_string(), vec![nest(f, n - 1, t)])
    } else {
        t
    }
}

//
// Character and alphabet helpers
//

/// Returns true if [chara] is a digit.
pub fn number(chara: char) -> bool {
    chara.is_ascii_digit()
}

/// Returns true if [chara] is an uppercase letter.
pub fn large(chara: char) -> bool {
    chara.is_ascii_uppercase()
}

/// Returns true if [chara] is a lowercase letter.
pub fn small(chara: char) -> bool {
    chara.is_ascii_lowercase()
}

/// Returns true if [chara] is one of the specified symbols.
pub fn symbol(chara: char) -> bool {
    matches!(chara, '+' | '*' | '!' | '?' | '-' | '/' | '^' | '$' | '%' | '&')
}

/// Returns true if [chara] is alphanumeric or one of the allowed symbols.
pub fn alphabet(chara: char) -> bool {
    number(chara) || large(chara) || small(chara) || symbol(chara)
}

//
// Parsing functions
//
// (These functions use simple string–slicing and will panic with "ParseError" on failure.)
//

/// [parsevarsym s] parses a variable symbol from the string [s].
pub fn parsevarsym(s: &str) -> String {
    if s.is_empty() {
        "".to_string()
    } else {
        let mut chars = s.chars();
        let first = chars.next().unwrap();
        let rest = parsevarsym(&s[first.len_utf8()..]);
        if first == ' ' && rest.is_empty() {
            "".to_string()
        } else if alphabet(first) {
            format!("{}{}", &s[0..first.len_utf8()], rest)
        } else {
            panic!("ParseError")
        }
    }
}

/// [parsefunsym s] parses a function symbol from [s].
pub fn parsefunsym(s: &str) -> String {
    if s.is_empty() {
        "".to_string()
    } else {
        let mut chars = s.chars();
        let first = chars.next().unwrap();
        if first == '(' {
            "".to_string()
        } else if first == ' ' {
            let rest = parsefunsym(&s[first.len_utf8()..]);
            if rest.is_empty() {
                "".to_string()
            } else {
                panic!("ParseError")
            }
        } else if alphabet(first) {
            format!("{}{}", &s[0..first.len_utf8()], parsefunsym(&s[first.len_utf8()..]))
        } else {
            panic!("ParseError")
        }
    }
}

/// [parseargexpssub s n] is a helper that parses a (possibly parenthesized) list of argument expressions.
/// It returns a tuple of a string and a vector of strings.
pub fn parseargexpssub(s: &str, n: i32) -> (String, Vec<String>) {
    if s.is_empty() {
        if n == 0 {
            ("".to_string(), vec![])
        } else {
            panic!("ParseError")
        }
    } else {
        let first = s.chars().next().unwrap();
        let rest = &s[first.len_utf8()..];
        match (n, first) {
            (0, ' ') => {
                let (s_prime, exps) = parseargexpssub(rest, 0);
                if s_prime == "" {
                    ("".to_string(), exps)
                } else {
                    panic!("ParseError")
                }
            }
            (0, '(') => {
                let (exp, mut exps) = parseargexpssub(rest, 1);
                let mut new_exps = vec![exp];
                new_exps.append(&mut exps);
                ("".to_string(), new_exps)
            }
            (0, _) => panic!("ParseError"),
            (1, ')') => {
                let (s_prime, exps) = parseargexpssub(rest, 0);
                if s_prime == "" && exps.is_empty() {
                    ("".to_string(), vec![])
                } else {
                    panic!("ParseError")
                }
            }
            (1, ',') => {
                let (exp, mut exps) = parseargexpssub(rest, 1);
                let mut new_exps = vec![exp];
                new_exps.append(&mut exps);
                ("".to_string(), new_exps)
            }
            (n_val, '(') => {
                let (s_prime, exps) = parseargexpssub(rest, n_val + 1);
                (format!("{}{}", first, s_prime), exps)
            }
            (n_val, ')') => {
                let (s_prime, exps) = parseargexpssub(rest, n_val - 1);
                (format!("{}{}", first, s_prime), exps)
            }
            (n_val, _) => {
                let (s_prime, exps) = parseargexpssub(rest, n_val);
                (format!("{}{}", first, s_prime), exps)
            }
        }
    }
}

/// [parseargexps exp] parses a list of argument expressions from [exp].
pub fn parseargexps(exp: &str) -> Vec<String> {
    let (s, exps) = parseargexpssub(exp, 0);
    if s == "" {
        exps
    } else {
        panic!("ParseError")
    }
}

/// [parsevar exp] parses a variable from [exp].
pub fn parsevar(exp: &str) -> Term {
    let s = exp.trim_start();
    if s.is_empty() {
        panic!("ParseError")
    } else {
        Term::Variable(VarSym(parsevarsym(s), 0))
    }
}

/// [parsefun exp] parses a function term from [exp].
pub fn parsefun(exp: &str) -> Term {
    let s = exp.trim_start();
    if s.is_empty() {
        panic!("ParseError")
    } else {
        Term::Function(parsefunsym(s), parseargs(s))
    }
}

/// [parseargs exp] parses the argument list from [exp].
pub fn parseargs(exp: &str) -> Vec<Term> {
    let s = exp.trim_start();
    if s.is_empty() {
        vec![]
    } else {
        let first = s.chars().next().unwrap();
        match first {
            ' ' => parseargs(&s[first.len_utf8()..]),
            '(' => {
                let args_strs = parseargexps(s);
                args_strs.into_iter().map(|s| parseterm(&s)).collect()
            }
            _ => parseargs(&s[first.len_utf8()..]),
        }
    }
}

/// [parseterm exp] parses a term from [exp].
pub fn parseterm(exp: &str) -> Term {
    let s = exp.trim_start();
    if s.is_empty() {
        panic!("ParseError")
    } else {
        let first = s.chars().next().unwrap();
        if small(first) {
            parsevar(s)
        } else if large(first) || number(first) || symbol(first) {
            parsefun(s)
        } else {
            panic!("ParseError")
        }
    }
}

/// Splits a string [s] into parts using the delimiter [delim].
pub fn parsetermtuplesub(delim: &str, s: &str) -> Vec<String> {
    s.split(delim).map(|part| part.to_string()).collect()
}

/// [parsetermtuple delim exp] parses a tuple of two terms separated by [delim].
pub fn parsetermtuple(delim: &str, exp: &str) -> (Term, Term) {
    let parts = parsetermtuplesub(delim, exp);
    if parts.len() == 2 {
        (parseterm(&parts[0]), parseterm(&parts[1]))
    } else {
        panic!("ParseError")
    }
}

/// [parserule exp] parses a rewrite rule (with "->" as the delimiter).
pub fn parserule(exp: &str) -> Rule {
    parsetermtuple("->", exp)
}

/// [parseeq exp] parses an equation (with "=" as the delimiter).
pub fn parseeq(exp: &str) -> Equation {
    parsetermtuple("=", exp)
}

/// [parserules ls] maps [parserule] over a list of strings.
pub fn parserules(ls: Vec<&str>) -> RuleSet {
    ls.into_iter().map(|s| parserule(s)).collect()
}

/// [parseeqs ls] maps [parseeq] over a list of strings.
pub fn parseeqs(ls: Vec<&str>) -> EquationSet {
    ls.into_iter().map(|s| parseeq(s)).collect()
}

//
// Converting terms and rules to strings and printing them
//

/// [strterm t] returns a string representation of [t].
pub fn strterm(t: &Term) -> String {
    match t {
        Term::Variable(VarSym(x, i)) if *i == 0 => x.clone(),
        Term::Variable(VarSym(x, i)) => format!("{}_{}", x, i),
        Term::Function(f, ts) => {
            if ts.is_empty() {
                f.clone()
            } else {
                format!("{}({})", f, strtermlist(ts))
            }
        }
    }
}

/// [strtermlist ts] returns a comma–separated string representation of [ts].
pub fn strtermlist(ts: &[Term]) -> String {
    ts.iter().map(|t| strterm(t)).collect::<Vec<_>>().join(", ")
}

/// [strrule rule] returns a string representation of a rule.
pub fn strrule(rule: &Rule) -> String {
    let (l, r) = rule;
    format!("{} -> {}", strterm(l), strterm(r))
}

/// [streq eq] returns a string representation of an equation.
pub fn streq(eq: &Equation) -> String {
    let (l, r) = eq;
    format!("{} = {}", strterm(l), strterm(r))
}

/// [strtermtuplessub f xs] helps format a list by applying [f] to each element.
pub fn strtermtuplessub<F, T>(f: F, xs: &[T]) -> String
where
    F: Fn(&T) -> String,
{
    if xs.is_empty() {
        " }".to_string()
    } else {
        let mut s = String::new();
        for x in xs {
            s.push_str(&format!("\n  {}", f(x)));
        }
        s + " }"
    }
}

/// [strtermtuples f xs] formats a list [xs] as a tuple using [f] on each element.
pub fn strtermtuples<F, T>(f: F, xs: &[T]) -> String
where
    F: Fn(&T) -> String,
{
    if xs.is_empty() {
        "{ }".to_string()
    } else {
        format!("{{ {}{}", f(&xs[0]), strtermtuplessub(&f, &xs[1..]))
    }
}

/// [strrules rs] returns a string representation of a ruleset.
pub fn strrules(rs: &RuleSet) -> String {
    strtermtuples(strrule, rs)
}

/// [streqs eqs] returns a string representation of an equationset.
pub fn streqs(eqs: &EquationSet) -> String {
    strtermtuples(streq, eqs)
}

/// [printterm t] prints [t] to standard output.
pub fn printterm(t: &Term) {
    println!("{}", strterm(t));
}

/// [printrule rule] prints a rule.
pub fn printrule(rule: &Rule) {
    println!("{}", strrule(rule));
}

/// [printeq eq] prints an equation.
pub fn printeq(eq: &Equation) {
    println!("{}", streq(eq));
}

/// [printrules rs] prints a ruleset.
pub fn printrules(rs: &RuleSet) {
    println!("{}", strrules(rs));
}

/// [printeqs eqs] prints an equationset.
pub fn printeqs(eqs: &EquationSet) {
    println!("{}", streqs(eqs));
}
