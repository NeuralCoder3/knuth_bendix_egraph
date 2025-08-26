% contrived_expansion_trip.p
% A contrived size-increasing axiom that produces three summands per match.

fof(expansion_trip_axiom,axiom,![X,Y,Z] : ( times(X, times(Y,Z)) = plus(times(times(X,Y),Z), times(Y, times(X,Z)), times(Z, times(X,Y))) )).

fof(conj_trip,conjecture,times(a,times(b,times(c,d))) = plus(times(times(times(a,b),c),d), plus(times(c,times(times(a,b),d)), plus(times(d,times(times(a,b),c)), plus(times(times(b,a),times(c,d)), plus(times(a,times(b,times(c,d))), plus(times(times(c,d),times(b,a)), plus(times(times(times(c,d),a),b), plus(times(a,times(times(c,d),b)), times(b,times(times(c,d),a))))))))))).

