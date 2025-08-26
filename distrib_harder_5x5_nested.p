% distrib_harder_5x5_nested.p
% 5x5 full expansion with extra algebraic axioms (annihilator, unit) + distributivity
% This is larger (25 product terms) and uses nested plus forms to encourage many rewrites

fof(plus_assoc,axiom,![X,Y,Z] : ( plus(X, plus(Y,Z)) = plus(plus(X,Y), Z) )).

fof(plus_comm,axiom,![X,Y] : ( plus(X,Y) = plus(Y,X) )).

fof(left_distrib,axiom,![X,Y,Z] : ( times(X, plus(Y,Z)) = plus(times(X,Y), times(X,Z)) )).

fof(right_distrib,axiom,![X,Y,Z] : ( times(plus(X,Y), Z) = plus(times(X,Z), times(Y,Z)) )).

fof(zero_annih,axiom,![X] : ( times(X, zero) = zero )).

fof(one_unit,axiom,![X] : ( times(X, one) = X )).

fof(conj_5x5,conjecture,times(plus(a, plus(b, plus(c, plus(d,e)))), plus(f, plus(g, plus(h, plus(i,j))))) = plus(times(a,f), plus(times(a,g), plus(times(a,h), plus(times(a,i), plus(times(a,j), plus(times(b,f), plus(times(b,g), plus(times(b,h), plus(times(b,i), plus(times(b,j), plus(times(c,f), plus(times(c,g), plus(times(c,h), plus(times(c,i), plus(times(c,j), plus(times(d,f), plus(times(d,g), plus(times(d,h), plus(times(d,i), plus(times(d,j), plus(times(e,f), plus(times(e,g), plus(times(e,h), plus(times(e,i), times(e,j)))))))))))))))))))))))))).

