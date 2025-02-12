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