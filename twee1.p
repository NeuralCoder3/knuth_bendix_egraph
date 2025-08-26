cnf(1, axiom, (f(X,f(Y,Z))=f(Y,f(X,Z)))).
% cnf(goal, conjecture, f(A,f(B,f(C,f(D,E))))=f(A,f(B,f(D,f(C,E))))).
cnf(goal, conjecture, f(A,f(B,f(C,f(D,f(E,f(F,f(G,H)))))))=f(A,f(B,f(C,f(D,f(E,f(G,f(F,H)))))))).
% https://pure.manchester.ac.uk/ws/portalfiles/portal/280559728/FULL_TEXT.PDF#:~:text=Example%205,there%20are%206942%20possible%20preorders