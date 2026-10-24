#!/usr/bin/env python3
"""f_N = sum_{a<c} sigma(x_c - x_a + sum_{l>c} sigma(x_l - x_c))  (C(N,2) out-star faces).
(1) exact: Delta_rho f_N == Delta_rho max_N on every locality class (all m >= 3);
(2) floating: is max_N - f_N in the span of affine + auxiliary functions?  (least squares residual)"""
import sys, itertools, numpy as np
import loctests as L
def fkeys(N):
    ks = []
    for a, c in itertools.combinations(range(N), 2):
        ks.append(L.tc.norm(N, [(c, a)], [(l, c) for l in range(c + 1, N)]))
    return ks
def ev(key, x):
    return max(0, L.A(key, x))
for N in range(3, int(sys.argv[1]) + 1):
    ks = fkeys(N)
    bad = 0
    for T, o in L.classes(N):
        if sum(L.delta(k, N, T, o) for k in ks) != L.maxN_delta(N, T, o): bad += 1
    rng = np.random.default_rng(1)
    X = rng.standard_normal((4000, N))
    aux = [np.ones(len(X))] + [X[:, i] for i in range(N)] + [np.maximum(X[:, i], 0) for i in range(N)] \
        + [np.maximum(X[:, i] - X[:, j], 0) for i in range(N) for j in range(N) if i != j]
    Aux = np.array(aux).T
    y = X.max(1) - np.array([sum(ev(k, x) for k in ks) for x in X])
    res = np.linalg.lstsq(Aux, y, rcond=None)
    r = y - Aux @ res[0]
    print(f'N={N}: units {len(ks)}; locality classes violating Delta f = Delta max: {bad}/{len(L.classes(N))}; '
          f'lstsq residual of (max - f) on aux span: {np.linalg.norm(r)/np.linalg.norm(y):.3e}')
