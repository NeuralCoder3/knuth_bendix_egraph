% distrib_6x6.p
% Full 6x6 distributive expansion (36 product terms)

fof(plus_assoc,axiom,![X,Y,Z] : ( plus(X, plus(Y,Z)) = plus(plus(X,Y), Z) )).

fof(plus_comm,axiom,![X,Y] : ( plus(X,Y) = plus(Y,X) )).

fof(left_distrib,axiom,![X,Y,Z] : ( times(X, plus(Y,Z)) = plus(times(X,Y), times(X,Z)) )).

fof(right_distrib,axiom,![X,Y,Z] : ( times(plus(X,Y), Z) = plus(times(X,Z), times(Y,Z)) )).

fof(conj_6x6,conjecture,times(plus(a, plus(b, plus(c, plus(d, plus(e, f))))), plus(g, plus(h, plus(i, plus(j, plus(k, l)))))) = plus(times(a,g), plus(times(a,h), plus(times(a,i), plus(times(a,j), plus(times(a,k), plus(times(a,l), plus(times(b,g), plus(times(b,h), plus(times(b,i), plus(times(b,j), plus(times(b,k), plus(times(b,l), plus(times(c,g), plus(times(c,h), plus(times(c,i), plus(times(c,j), plus(times(c,k), plus(times(c,l), plus(times(d,g), plus(times(d,h), plus(times(d,i), plus(times(d,j), plus(times(d,k), plus(times(d,l), plus(times(e,g), plus(times(e,h), plus(times(e,i), plus(times(e,j), plus(times(e,k), plus(times(e,l), plus(times(f,g), plus(times(f,h), plus(times(f,i), plus(times(f,j), plus(times(f,k), times(f,l))))))))))))))))))))))))))))))))))))).

