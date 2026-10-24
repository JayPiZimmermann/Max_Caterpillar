"""EXACT, independent re-check of the key step of k(5) >= 2:
a translation-invariant g = <l,x> + sum_{i<j} a_ij relu(x_i - x_j) (sum l = 0) that vanishes
identically on every 3-locality cell C_{T,rho} = {x_t = s (t in T), s > x_rho1 > x_rho2} is zero.
Unknowns: l (5), a (10).  On C_{T,rho}, g is linear in (s, x_rho1, x_rho2); all three coefficients
must vanish.  Prints the nullspace dimension (0 expected) for N = 3, 4, 5."""
import itertools, sympy, sys
for N in (3, 4, 5):
    P = list(itertools.combinations(range(N), 2)); nv = N + len(P)
    rows = [[1] * N + [0] * len(P)]
    for T in itertools.combinations(range(N), 3):
        O = [v for v in range(N) if v not in T]
        for order in itertools.permutations(O):
            # variables of the cell: s (index 0), x_order[k] (index k+1); x_t = s
            pos = {t: 0 for t in T}; pos.update({o: k + 1 for k, o in enumerate(order)})
            height = {t: 0 for t in T}; height.update({o: k + 1 for k, o in enumerate(order)})  # 0 = top
            M = [[0] * nv for _ in range(1 + len(O))]
            for i in range(N):
                M[pos[i]][i] += 1
            for q, (i, j) in enumerate(P):
                if height[i] < height[j]:      # x_i > x_j on the cell: relu = x_i - x_j
                    M[pos[i]][N + q] += 1; M[pos[j]][N + q] -= 1
                elif height[j] < height[i]:    # relu(x_i - x_j) = 0
                    pass
                # equal heights (both in T): relu(0) = 0
            rows += M
    ns = sympy.Matrix(rows).nullspace()
    print('N', N, 'equations', len(rows), 'unknowns', nv, 'nullspace dim', len(ns))
