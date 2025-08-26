% distrib_7x7.p
% Full 7x7 distributive expansion (49 product terms)

fof(plus_assoc,axiom,![X,Y,Z] : ( plus(X, plus(Y,Z)) = plus(plus(X,Y), Z) )).

fof(plus_comm,axiom,![X,Y] : ( plus(X,Y) = plus(Y,X) )).

fof(left_distrib,axiom,![X,Y,Z] : ( times(X, plus(Y,Z)) = plus(times(X,Y), times(X,Z)) )).

fof(right_distrib,axiom,![X,Y,Z] : ( times(plus(X,Y), Z) = plus(times(X,Z), times(Y,Z)) )).

fof(conj_7x7,conjecture,times(plus(a, plus(b, plus(c, plus(d, plus(e, plus(f, g)))))), plus(h, plus(i, plus(j, plus(k, plus(l, plus(m, n))))))) = plus(times(a,h), plus(times(a,i), plus(times(a,j), plus(times(a,k), plus(times(a,l), plus(times(a,m), plus(times(a,n), plus(times(b,h), plus(times(b,i), plus(times(b,j), plus(times(b,k), plus(times(b,l), plus(times(b,m), plus(times(b,n), plus(times(c,h), plus(times(c,i), plus(times(c,j), plus(times(c,k), plus(times(c,l), plus(times(c,m), plus(times(c,n), plus(times(d,h), plus(times(d,i), plus(times(d,j), plus(times(d,k), plus(times(d,l), plus(times(d,m), plus(times(d,n), plus(times(e,h), plus(times(e,i), plus(times(e,j), plus(times(e,k), plus(times(e,l), plus(times(e,m), plus(times(e,n), plus(times(f,h), plus(times(f,i), plus(times(f,j), plus(times(f,k), plus(times(f,l), plus(times(f,m), plus(times(f,n), plus(times(g,h), plus(times(g,i), plus(times(g,j), plus(times(g,k), plus(times(g,l), plus(times(g,m), times(g,n)))))))))))))))))))))))))))))))))))))))))))))))))).

