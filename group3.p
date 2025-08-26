cnf(1, axiom, ('1' * A = A)).
cnf(2, axiom, ((A*B)*C = A*(B*C))).
cnf(3, axiom, (i(A) * A = '1')).
cnf(4, axiom, (f(A*B)=f(A)*f(B))).
cnf(5, axiom, (g(A*B)=g(A)*g(B))).
cnf(6, axiom, (f(A)*g(B)=g(B)*f(A))).
cnf(goal, conjecture, f(x)*(g(y)*z)=g(y)*(f(x)*z)).