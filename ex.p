cnf(1, axiom, A / B = A * p(B, '-1')).
cnf(2, axiom, A * '0' = '0').
cnf(3, axiom, A * B = B * A).
cnf(goal, conjecture, '0' / X = '0').