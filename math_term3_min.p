cnf(1, axiom, (add(A,B) = add(B,A))).
cnf(2, axiom, (mul(A,B) = mul(B,A))).
cnf(7, axiom, (add(A,zero) = A)).
cnf(8, axiom, (mul(X,zero) = zero)).
cnf(9, axiom, (mul(X,one) = X)).

cnf(goal, conjecture, mul(b, add(zero, mul(x, add(add(add(mul(x, one), sub(pow(y, zero), div(mul(zero, z), pow(a, one)))), div(pow(pow(b, one), one), mul(one, one))), div(mul(d, zero), pow(e, one)))))) = mul(b, add(zero, mul(x, add(add(add(x, sub(pow(y, zero), div(mul(zero, z), pow(a, one)))), div(pow(pow(b, one), one), one)), div(zero, pow(e, one))))))).
