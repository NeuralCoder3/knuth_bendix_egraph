% distrib_complex.p
% A more complex problem that expands (a + (b + c)) * (d + (e + f))
% into the full 3x3 product using repeated distributivity.  This forces many rewrites
% and, in completion-based provers with KBO, can be hard to orient/terminate.

fof(plus_assoc,axiom,![X,Y,Z] : ( plus(X, plus(Y,Z)) = plus(plus(X,Y), Z) )).

fof(plus_comm,axiom,![X,Y] : ( plus(X,Y) = plus(Y,X) )).

fof(left_distrib,axiom,![X,Y,Z] : ( times(X, plus(Y,Z)) = plus(times(X,Y), times(X,Z)) )).

fof(right_distrib,axiom,![X,Y,Z] : ( times(plus(X,Y), Z) = plus(times(X,Z), times(Y,Z)) )).

fof(conj_expand_3x3,conjecture,times(plus(a, plus(b, c)), plus(d, plus(e, f))) = plus(times(a,d), plus(times(a,e), plus(times(a,f), plus(times(b,d), plus(times(b,e), plus(times(b,f), plus(times(c,d), plus(times(c,e), times(c,f)))))))))).

