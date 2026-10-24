#!/usr/bin/env python3
"""Mixed hierarchical functionals.  Delta_t f (z') = f(z', z_t = -D) - f(z', z_t = +D) with D huge
(= the limit L_t f - U_t f on germs, step 12).  Features of a germ g:
  (i)  for each normalised (m-1)-anchor orbit O (entries <= k1): sum_t sum_{y in O} U'_y [Delta_t g];
  (ii) for each normalised m-anchor orbit (entries <= k2): sum_{y in O} U_y g.
Both are symmetric functionals; (i) are limits of MDs with one huge step.  Test: does a combination
separate max from twin germs, with k1, k2 FIXED while R grows?
Usage: twin_hier.py m R k1 k2 [fam]"""
import sys, itertools, time
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from twin_lib import eval_germ, orbit, rank_mod_p
from twin_wbar import anchors, ufeat
import sym_md
m, R, k1, k2 = map(int, sys.argv[1:5])
fn = sys.argv[5] if len(sys.argv) > 5 else 'twin'
sym_md.MODE['pred'] = sym_md.twin_leaves if fn == 'twin' else sym_md.two_outleaves
fam = sym_md.family(m, R)
D = 10 ** 7
n = m - 1
cube = np.array(list(itertools.product([0, 1], repeat=n)), dtype=np.int64)
sign = np.array([(-1) ** (n - int(s.sum())) for s in cube], dtype=np.int64)
reps1 = anchors(n, k1)
blocks = [np.array(orbit(p), dtype=np.int64) for p in reps1]
sizes = [len(b) for b in blocks]; idx = np.repeat(np.arange(len(reps1)), sizes)
Y = np.concatenate(blocks); Zr = (Y[:, None, :] + cube[None, :, :]).reshape(-1, n)
Zs = []
for t in range(m):
    for sgn in (-1, 1):
        Z = np.insert(Zr, t, sgn * D, axis=1); Zs.append(Z)
Zall = np.concatenate(Zs); npt = len(Zr)

def feat1(f):
    vals = f(Zall).reshape(m, 2, npt)
    dif = (vals[:, 0, :] - vals[:, 1, :]).sum(axis=0)          # sum_t Delta_t
    per = dif.reshape(len(Y), len(cube)) @ sign
    return np.bincount(idx, weights=per, minlength=len(reps1)).round().astype(np.int64)

reps2 = anchors(m, k2) if k2 >= 0 else []
def feat(f):
    a = list(feat1(f))
    if reps2: a += ufeat(m, reps2, f)
    return a
t0 = time.time()
A = np.array([feat(lambda Z, v=v, F=F: eval_germ(v, F, Z)) for v, F in fam]).T
b = np.array(feat(lambda Z: Z.max(axis=1)))
r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, b[:, None]], 1))
print(f'm={m} R={R} k1={k1} k2={k2} {fn}: {len(fam)} germs, {A.shape[0]} features, rank {r1}, with max {r2} ->',
      'SEPARATED' if r2 > r1 else 'not separated', f'({time.time()-t0:.0f}s)', flush=True)
