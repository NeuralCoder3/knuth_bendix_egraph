cnf(1, axiom, ('1' * A = A)).
cnf(2, axiom, ((A*B)*C = A*(B*C))).
cnf(3, axiom, (i(A) * A = '1')).
cnf(4, axiom, (g(A*B)=g(A)*g(B))).
cnf(5, axiom, (f(A)*g(B)=g(B)*f(A))).
cnf(6, axiom, (p(A,B) = A*B)).
cnf(goal, conjecture, g(i(B))*(f(A)*g(B))=f(A)).