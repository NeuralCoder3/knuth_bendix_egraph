// use std::fmt;
// use std::error::Error;

use symbol_table::GlobalSymbol;

pub type FunSym = GlobalSymbol;
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarSym(pub GlobalSymbol, pub i32);
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
pub type Weight = Vec<(FunSym, usize)>;


#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StagedVec<T> {
    pub current: Vec<T>,
    pub staged: Vec<T>,
}

impl<T> StagedVec<T> {
    pub fn new(current: Vec<T>) -> Self {
        Self { current, staged: Vec::new() }
    }

    pub fn rebuild(current: Vec<T>, staged: Vec<T>) -> Self {
        Self { current, staged }
    }

    // Iterate current only (drop-in replacement for previous .iter())
    // pub fn iter(&self) -> impl Iterator<Item = &T> {
    //     self.current.iter()
    // }

    // Iterate current + staged without allocating
    pub fn iter_all(&self) -> impl Iterator<Item = &T> {
        self.current.iter().chain(self.staged.iter())
    }

    // pub fn extend_staged<I: IntoIterator<Item = T>>(&mut self, it: I) {
    //     self.staged.extend(it);
    // }

    pub fn commit(&mut self) {
        self.current.extend(self.staged.drain(..));
    }
}


// impl<T> Clone for StagedVec<T> where T: Clone {
//     fn clone(&self) -> Self {
//         Self { current: self.current.clone(), staged: self.staged.clone() }
//     }
// }


// /// Error type to indicate that the completion process failed.
// #[derive(Debug)]
// pub struct CompletionFailed;

// impl fmt::Display for CompletionFailed {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(f, "CompletionFailed")
//     }
// }

// impl Error for CompletionFailed {}