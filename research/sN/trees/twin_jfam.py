#!/usr/bin/env python3
"""Wall-density functionals.  J_12 f (p) = [f(p+eps u) + f(p-eps u) - 2 f(p)]/eps, u = e1 - e2, p in H_12
(here p_1 = p_2 = 0 by diagonal invariance).  Psi_{box} f = (m-2)-dim mixed difference of y -> J_12 f(0,0,y)
over a box in the coordinates 3..m.  These kill W_m (functions independent of one coordinate).
Symmetrised: Phi(g) = sum_{pi in S_m} Psi(g o pi).  Test: is max separated from the twin family?
Usage: twin_jfam.py m R ntests [seed]"""
import sys, itertools, random
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from twin_lib import eval_germ, rank_mod_p
import sym_md

m, R, nt = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
sym_md.MODE['pred'] = sym_md.twin_leaves
fam = sym_md.family(m, R)
rng = random.Random(seed)
SC = 1000
n = m - 2
corners = list(itertools.product([0, 1], repeat=n))
csign = [(-1) ** (n - sum(c)) for c in corners]
pts = []      # (test index, sign, point)
for t in range(nt):
    x = [rng.randint(-20, 20) for _ in range(n)]
    d = [rng.randint(1, 20) for _ in range(n)]
    for c, s in zip(corners, csign):
        y = [SC * (x[k] + d[k] * c[k]) + rng.choice([0]) for k in range(n)]
        pts.append((t, s, y))
# perturb to avoid exact ties: add distinct small offsets (still >> eps)
base = np.array([[0, 0] + y for _, _, y in pts], dtype=np.int64)
base[:, 2:] += np.array([[7 * (k + 1) + 13 * i % 97 for k in range(n)] for i in range(len(pts))])
u = np.zeros(m, dtype=np.int64); u[0] = 1; u[1] = -1
Zp, Zm = base + u, base - u
tidx = np.array([t for t, _, _ in pts]); sg = np.array([s for _, s, _ in pts])
perms = list(itertools.permutations(range(m)))

def J(fn):
    return fn(Zp) + fn(Zm) - 2 * fn(base)

def feat(fn):
    vals = J(fn) * sg
    return np.bincount(tidx, weights=vals, minlength=nt).round().astype(np.int64)

cols = []
for v, F in fam:
    tot = np.zeros(nt, dtype=np.int64)
    for p in perms:   # g o pi: coordinate t of g reads z_{p[t]}
        vv = [0] * m
        for t in range(m): vv[p[t]] = v[t]
        FF = [(p[i], p[j]) for i, j in F]
        tot += feat(lambda Z: eval_germ(vv, FF, Z))
    cols.append(tot)
A = np.array(cols).T
b = feat(lambda Z: Z.max(axis=1)) * len(perms)
r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, b[:, None]], 1))
print(f'm={m} R={R} J-family: {len(fam)} germ reps, {nt} tests; rank {r1}, with max {r2} ->', 'SEPARATED' if r2 > r1 else 'not separated', flush=True)
