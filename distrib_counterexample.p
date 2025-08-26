% distrib_counterexample.p
% A small problem showing both left- and right-distributivity
% plus is associative and commutative; times distributes over plus from both sides.

fof(plus_assoc,axiom,![X,Y,Z] : ( plus(X, plus(Y,Z)) = plus(plus(X,Y), Z) )).

fof(plus_comm,axiom,![X,Y] : ( plus(X,Y) = plus(Y,X) )).

fof(left_distrib,axiom,![X,Y,Z] : ( times(X, plus(Y,Z)) = plus(times(X,Y), times(X,Z)) )).

fof(right_distrib,axiom,![X,Y,Z] : ( times(plus(X,Y), Z) = plus(times(X,Z), times(Y,Z)) )).

fof(conj_expand_2x2,conjecture,times(plus(a, b), plus(c, d)) = plus(plus(times(a,c), times(a,d)), plus(times(b,c), times(b,d)))).

