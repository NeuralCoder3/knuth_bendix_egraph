% distrib_hard_4x4.p
% 4x4 full distributive expansion with associative+commutative plus
% left and right distributivity for times over plus; ACA-style conditions

fof(plus_assoc,axiom,![X,Y,Z] : ( plus(X, plus(Y,Z)) = plus(plus(X,Y), Z) )).

fof(plus_comm,axiom,![X,Y] : ( plus(X,Y) = plus(Y,X) )).

fof(times_assoc,axiom,![X,Y,Z] : ( times(X, times(Y,Z)) = times(times(X,Y), Z) )).

fof(left_distrib,axiom,![X,Y,Z] : ( times(X, plus(Y,Z)) = plus(times(X,Y), times(X,Z)) )).

fof(right_distrib,axiom,![X,Y,Z] : ( times(plus(X,Y), Z) = plus(times(X,Z), times(Y,Z)) )).

fof(conj_4x4,conjecture,times(plus(a, plus(b, plus(c,d))), plus(e, plus(f, plus(g,h)))) = plus(times(a,e), plus(times(a,f), plus(times(a,g), plus(times(a,h), plus(times(b,e), plus(times(b,f), plus(times(b,g), plus(times(b,h), plus(times(c,e), plus(times(c,f), plus(times(c,g), plus(times(c,h), plus(times(d,e), plus(times(d,f), plus(times(d,g), times(d,h))))))))))))))))).

