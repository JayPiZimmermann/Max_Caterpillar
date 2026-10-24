#!/usr/bin/env python3
"""Find a small set of symmetric patterns separating max from the family; print the functional.
Usage: sym_extract.py m R values"""
import sys, itertools
import numpy as np
from fractions import Fraction
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from sym_md import family, eval_germ, patterns, orbit
from pn_test import rank_mod_p, P
m, R = int(sys.argv[1]), int(sys.argv[2])
values = [int(x) for x in sys.argv[3].split(',')]
fam = family(m, R)
pats = patterns(m, values)
cube = np.array(list(itertools.product([0, 1], repeat=m)), dtype=np.int64)
sign = np.array([(-1) ** (m - int(s.sum())) for s in cube], dtype=np.int64)
def feat(fn):
    out = []
    for p in pats:
        D = np.array(orbit(p), dtype=np.int64)
        Z = (D[:, None, :] * cube[None, :, :]).reshape(-1, m)
        out.append(int((fn(Z).reshape(len(D), len(cube)) @ sign).sum()))
    return out
A = np.array([feat(lambda Z, v=v, F=F: eval_germ(v, F, Z)) for v, F in fam], dtype=object).T
b = np.array(feat(lambda Z: Z.max(axis=1)), dtype=object)
def sep(idx):
    if not idx: return False
    M = np.array(A[idx], dtype=np.int64); bb = np.array(b[idx], dtype=np.int64)[:, None]
    return rank_mod_p(M) < rank_mod_p(np.concatenate([M, bb], axis=1))
idx = list(range(len(pats)))
assert sep(idx), 'not separated'
for i in list(idx):
    t = [j for j in idx if j != i]
    if sep(t): idx = t
print('minimal pattern set:', [pats[i] for i in idx])
# solve exactly: c over idx with c.A = 0, c.b = 1 (Fractions, Gaussian elimination)
rows = [[Fraction(int(A[i][g])) for g in range(A.shape[1])] + [Fraction(int(b[i]))] for i in idx]
# solve c^T [A | b] = [0 ... 0 | 1]: transpose system M c = e, M = [A|b]^T
ncol = len(idx); M = [[rows[i][g] for i in range(ncol)] for g in range(A.shape[1] + 1)]
rhs = [Fraction(0)] * A.shape[1] + [Fraction(1)]
# gaussian elimination
aug = [M[r] + [rhs[r]] for r in range(len(M))]
piv = []; r = 0
for cidx in range(ncol):
    pr = next((k for k in range(r, len(aug)) if aug[k][cidx] != 0), None)
    if pr is None: continue
    aug[r], aug[pr] = aug[pr], aug[r]
    pv = aug[r][cidx]; aug[r] = [x / pv for x in aug[r]]
    for k in range(len(aug)):
        if k != r and aug[k][cidx] != 0:
            f = aug[k][cidx]; aug[k] = [x - f * y for x, y in zip(aug[k], aug[r])]
    piv.append(cidx); r += 1
c = [Fraction(0)] * ncol
for k, cidx in enumerate(piv): c[cidx] = aug[k][-1]
print('functional (pattern: coefficient), normalised so Lambda(max) = 1:')
for i, ci in zip(idx, c): print('  ', pats[i], ci, ' orbit size', len(orbit(pats[i])))
