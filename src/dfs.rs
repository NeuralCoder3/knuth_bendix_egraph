mod kbo;
mod term_rewrite;
mod types;
mod util;

use crate::kbo::*;
use crate::term_rewrite::*;
use crate::types::*;




fn main() {
    let E = parseeqs(vec![
        // Group (Figure 3-1/3-2, page 25)
        // "Mul(One, x) = One",
        // "Mul(Mul(x, y), z) = Mul(x, Mul(y, z))",
        // "Mul(Inv(x), x) = One",
        "M(E, x) = x",
        "M(M(x, y), z) = M(x, M(y, z))",
        "M(I(x), x) = E",
        // One Group Endomorphism (Figure 7-1/7-2, page 51)
        "F(M(x, y)) = M(F(x), F(y))",
        // Two Commuting Endomorphisms (Figure 7-5/7-6, page 53)
        "G(M(x, y)) = M(G(x), G(y))",
        "M(F(x), G(y)) = M(G(y), F(x))",
        // Three Commuting Endomorphisms (https://github.com/iwehrman/Slothrop/blob/master/tests/cge3.tptp)
        "H(M(x, y)) = M(H(x), H(y))",
        "M(F(x), H(y)) = M(H(y), F(x))",
        "M(G(x), H(y)) = M(H(y), G(x))",
        // abelian group
        // "M(x, y) = M(y, x)", // commutativity
    ]);
    let t = parseterm("M(G(I(B)), M(F(A), G(B)))");
    println!("{}", strterm(&t));

    // fn dfs(t: &Term, E: &EquationSet) -> bool {

    // }
}