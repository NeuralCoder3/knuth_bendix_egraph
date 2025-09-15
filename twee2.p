cnf(1, axiom, (f(X,Y) = add(X,Y))).
cnf(2, axiom, noteq(Y,null) => (f(X,Y) = X)).
cnf(2, axiom, noteq(five,null)).
cnf(goal, conjecture, f(five,three) = five).

