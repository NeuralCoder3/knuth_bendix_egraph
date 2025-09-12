use crate::types::*;
use symbol_table::GlobalSymbol;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CnfKind {
    Axiom,
    Conjecture,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CnfStmt {
    pub name: String,
    pub kind: CnfKind,
    pub equation: Equation,
}

pub fn parse_p_file(path: &str) -> Vec<CnfStmt> {
    let content = std::fs::read_to_string(path).expect("failed to read .p file");
    parse_p_str(&content)
}

pub fn parse_p_str(content: &str) -> Vec<CnfStmt> {
    // Remove full-line comments starting with '%', keep others intact
    let mut stmts = Vec::new();
    let mut buf = String::new();
    let mut depth: i32 = 0; // parenthesis depth

    for raw_line in content.lines() {
        let line = match raw_line.find('%') {
            Some(idx) => &raw_line[..idx],
            None => raw_line,
        }.trim();
        if line.is_empty() || line.starts_with('%') { continue; }
        // accumulate and split on top-level '.'
        for ch in line.chars() {
            match ch {
                '(' => { depth += 1; buf.push(ch); }
                ')' => { depth -= 1; buf.push(ch); }
                '.' if depth == 0 => {
                    let stmt = buf.trim().to_string();
                    if !stmt.is_empty() { stmts.push(stmt); }
                    buf.clear();
                }
                _ => buf.push(ch),
            }
        }
        // whitespace between lines
        if !buf.ends_with(' ') { buf.push(' '); }
    }
    // Flush any leftover buffer if it ends with a complete cnf(...)
    let leftover = buf.trim();
    if leftover.starts_with("cnf(") && leftover.ends_with(')') {
        stmts.push(leftover.to_string());
    }
    let mut results = Vec::new();
    for s in stmts {
        if s.is_empty() { continue; }
        let s_trim = s.trim();
        let s_lower = s_trim.to_lowercase();
        if !s_lower.contains("cnf(") {
            continue; // ignore unknown statements
        }
        if let Some(stmt) = parse_cnf_stmt(s_trim) {
            results.push(stmt);
        }
    }
    results
}

fn parse_cnf_stmt(s: &str) -> Option<CnfStmt> {
    // s starts with cnf(
    // allow leading spaces before cnf(
    let s_trim = s.trim_start();
    let inside = s_trim.strip_prefix("cnf(")?;
    let (args_str, _) = split_cnf_args(inside)?;
    let mut parts = split_top_level_commas(args_str);
    if parts.len() != 3 { return None; }
    let name_owned = parts.remove(0);
    let name = trim_brackets(name_owned.trim()).to_string();
    let kind_raw = parts.remove(0).trim().to_lowercase();
    let kind = match kind_raw.as_str() {
        "axiom" => CnfKind::Axiom,
        "conjecture" => CnfKind::Conjecture,
        _ => return None,
    };
    let formula_owned = parts.remove(0);
    let mut formula = formula_owned.trim().to_string();
    while let Some(stripped) = strip_outer_parens(&formula) { formula = stripped.to_string(); }
    let (l_str, r_str) = split_top_level_eq(&formula)?;
    let l = parse_term_tptp(l_str.trim());
    let r = parse_term_tptp(r_str.trim());
    Some(CnfStmt { name, kind, equation: (l, r) })
}

fn trim_brackets(s: &str) -> &str {
    let t = s.trim();
    if let (Some('['), Some(']')) = (t.chars().next(), t.chars().last()) {
        &t[1..t.len()-1]
    } else {
        t
    }
}

fn split_top_level_until(s: &str, end: char) -> Option<(&str, &str)> {
    let mut depth = 0i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => { depth += 1; }
            _ if ch == end && depth == 0 => {
                return Some((&s[..i], &s[i+ch.len_utf8()..]));
            }
            ')' => { depth -= 1; }
            _ => {}
        }
    }
    None
}

fn split_top_level_commas(s: &str) -> Vec<String> {
    let mut res = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                res.push(s[start..i].to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    res.push(s[start..].to_string());
    res
}

fn split_top_level_eq(s: &str) -> Option<(&str, &str)> {
    let mut depth = 0i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            '=' if depth == 0 => {
                return Some((&s[..i], &s[i+1..]));
            }
            _ => {}
        }
    }
    None
}

// Split arguments of cnf( ... ) by finding the matching ')' for the opening after "cnf("
fn split_cnf_args(s: &str) -> Option<(&str, &str)> {
    // depth starts at 1 for the implicit opening before s
    let mut depth = 1i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 { return Some((&s[..i], &s[i+1..])); }
            }
            _ => {}
        }
    }
    None
}

fn strip_outer_parens(s: &str) -> Option<&str> {
    let st = s.trim();
    if !(st.starts_with('(') && st.ends_with(')')) { return None; }
    let mut depth = 0i32;
    for (i, ch) in st.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 && i != st.len()-1 { return None; }
            }
            _ => {}
        }
    }
    if depth == 0 { Some(&st[1..st.len()-1]) } else { None }
}

// TPTP-style term parser: Uppercase start => Variable, lowercase start => Function
fn parse_term_tptp(s: &str) -> Term {
    let s = s.trim();
    if s.is_empty() { panic!("ParseError: empty term"); }
    let mut it = s.char_indices().peekable();
    let first = it.peek().unwrap().1;
    if first.is_ascii_uppercase() { // Variable
        let ident = parse_ident(s);
        Term::Variable(VarSym(GlobalSymbol::from(ident), 0))
    } else if first.is_ascii_lowercase() { // Function or constant
        let name = parse_ident(s);
        let rest_slice = &s[name.len()..];
        let rest = rest_slice.trim_start();
        if rest.starts_with('(') {
            let (args_str, tail) = split_top_level_until(&rest[1..], ')').expect("Unclosed args");
            debug_assert!(tail.trim_start().is_empty());
            let args = if args_str.trim().is_empty() {
                vec![]
            } else {
                split_top_level_commas(args_str)
                    .into_iter()
                    .map(|a| parse_term_tptp(a.trim()))
                    .collect()
            };
            Term::Function(GlobalSymbol::from(name), args)
        } else {
            Term::Function(GlobalSymbol::from(name), vec![])
        }
    } else {
        panic!("ParseError: unexpected start of term: {}", s);
    }
}

fn parse_ident(s: &str) -> String {
    let mut end = 0usize;
    for (i, ch) in s.char_indices() {
        if ch.is_ascii_alphanumeric() || ch == '_' { end = i + ch.len_utf8(); } else { break; }
    }
    s[..end].to_string()
}


