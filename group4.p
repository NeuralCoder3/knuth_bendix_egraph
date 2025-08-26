cnf(ax_comm_xy, axiom, (x * y = y * x)).
cnf(ax_x_inv_x, axiom, (x * inv(x) = '1')).
cnf(ax_inv_x_x, axiom, (inv(x) * x = '1')).
cnf(ax_y_inv_y, axiom, (y * inv(y) = '1')).
cnf(ax_inv_y_y, axiom, (inv(y) * y = '1')).

cnf(ax_assoc, axiom, x * (y * z) = (x * y) * z).

% Conjecture: group is well-defined (e.g., 1 * x = x)
cnf(conj_identity, conjecture, '1' * x = x).