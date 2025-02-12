use crate::types::*;

//
// Helper functions on vectors
//

/// Returns the union of two vectors (without duplicates).
pub fn union<T: Clone + PartialEq>(mut v1: Vec<T>, v2: Vec<T>) -> Vec<T> {
    for item in v2 {
        if !v1.contains(&item) {
            v1.push(item);
        }
    }
    v1
}

/// Returns the intersection of two vectors.
pub fn intersection<T: Clone + PartialEq>(v1: Vec<T>, v2: Vec<T>) -> Vec<T> {
    v1.into_iter().filter(|x| v2.contains(x)).collect()
}

/// Subtracts all elements in `to_remove` from `v`.
pub fn subtraction<T: Clone + PartialEq>(v: Vec<T>, to_remove: Vec<T>) -> Vec<T> {
    v.into_iter().filter(|item| !to_remove.contains(item)).collect()
}

/// Finds a substitution for a variable in a substitution set.
/// only lifetime in code
pub fn find_substitution<'a>(xi: &'a VarSym, ss: &'a SubstitutionSet) -> Option<&'a Term> {
    for (var, term) in ss {
        if var == xi {
            return Some(term);
        }
    }
    None
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
