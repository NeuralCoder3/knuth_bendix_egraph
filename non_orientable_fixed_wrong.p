% non_orientable_fixed.p
% Corrected: conjecture computed by applying the expansion axiom twice

fof(expansion_axiom,axiom,![X,Y,Z] : ( times(X, times(Y,Z)) = plus(times(times(X,Y),Z), times(Y, times(X,Z))) )).

fof(conj_non_orient_fixed,conjecture,times(a,times(b,times(c,d))) = plus(times(times(times(a,b),c),d), plus(times(c,times(times(a,b),d)), plus(times(times(b,a),times(c,d)), times(a,times(b,times(c,d))))))).

