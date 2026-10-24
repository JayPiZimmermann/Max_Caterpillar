#!/usr/bin/env python3
"""Continuum closure probe.  For delta in the fundamental chamber (random, sum delta = 1), the symmetrised
MD transform  SF_f(delta) = sum_{sigma} sum_S (-1)^{m-|S|} f((sigma delta)_S).  SF_max = m! (-1)^{m+1} min.
Least-squares residual of SF_max against span{SF_g : g twin, heads <= R} in L^2(chamber sample).
If the relative residual tends to 0 as R grows, max is in the L^2-closure (no continuous uniform functional).
Usage: twin_l2.py m npts R1,R2,..."""
import sys, itertools, time
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
import sym_md
m, npts = int(sys.argv[1]), int(sys.argv[2]); Rs = [int(x) for x in sys.argv[3].split(',')]
sym_md.MODE['pred'] = sym_md.twin_leaves
rng = np.random.default_rng(3)
X = np.sort(rng.dirichlet(np.ones(m), size=npts), axis=1)
cube = np.array(list(itertools.product([0, 1], repeat=m)), dtype=float)
sign = np.array([(-1) ** (m - int(s.sum())) for s in cube], dtype=float)
perms = list(itertools.permutations(range(m)))
Z = np.concatenate([(X[:, p][:, None, :] * cube[None, :, :]).reshape(-1, m) for p in perms])
def SF(v, F):
    s = Z @ np.array(v, dtype=float)
    for i, j in F: s = s + np.maximum(Z[:, i] - Z[:, j], 0)
    s = np.maximum(s, 0).reshape(len(perms), npts, len(cube)) @ sign
    return s.sum(axis=0)
b = (Z.max(axis=1).reshape(len(perms), npts, len(cube)) @ sign).sum(axis=0)
fam = sym_md.family(m, max(Rs))
for R in Rs:
    t0 = time.time()
    cols = [SF(v, F) for v, F in fam if max(abs(x) for x in v) <= R]
    A = np.array(cols).T
    Q, Rr = np.linalg.qr(A)
    keep = np.abs(np.diag(Rr)) > 1e-9 * np.abs(np.diag(Rr)).max()
    Q = Q[:, keep]
    res = b - Q @ (Q.T @ b)
    print(f'm={m} R={R}: {A.shape[1]} germs, numerical rank {keep.sum()}, relative residual {np.linalg.norm(res)/np.linalg.norm(b):.3e} ({time.time()-t0:.0f}s)', flush=True)
