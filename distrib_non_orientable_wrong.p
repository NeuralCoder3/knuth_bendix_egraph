% distrib_non_orientable.p
% A theory with only LEFT distributivity and a size-increasing 'expansion' axiom
% This is intended to create rules that KBO cannot orient into terminating rewrite rules easily.

fof(plus_assoc,axiom,![X,Y,Z] : ( plus(X, plus(Y,Z)) = plus(plus(X,Y), Z) )).

fof(plus_comm,axiom,![X,Y] : ( plus(X,Y) = plus(Y,X) )).

fof(left_distrib,axiom,![X,Y,Z] : ( times(X, plus(Y,Z)) = plus(times(X,Y), times(X,Z)) )).

fof(expansion_axiom,axiom,![X,Y,Z] : ( times(X, times(Y,Z)) = plus(times(times(X,Y),Z), times(Y, times(X,Z))) )).

fof(conj_non_orient,conjecture,times(a, times(b, times(c,d))) = plus(times(times(times(a,b),c),d), plus(times(times(b,times(a,c)),d), plus(times(b, times(times(a,c),d)), times(b, times(c, times(a,d))))))).

