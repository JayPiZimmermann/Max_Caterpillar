#!/usr/bin/env python3
"""Make the F1 dual certificate of lp.py exact at every top size.

lp.py treats T-germs with |T| > tmax_exact as nonzero (conservative for the
primal, NOT for the dual).  This script takes the dual support units of the
F1 optimum and recomputes their rows with exact classes for every |T| (cell
method on |T| variables), then re-checks dual feasibility A^T y >= 1 exactly.
With a second argument 'sample', nonzero classes are certified instead by
exact integer rank on random sample points (sound for "nonzero": a rank
increase on samples is a rank increase on R^t), which is what dual
feasibility needs (true hits >= counted hits).
Usage: python3 check_dual_f1.py N [sample]
"""
import math
import pickle
import sys
from fractions import Fraction

from germs import class_coords
from lp import solve
import random
import flint


def sampled_nonzero(t, g, ns=None, seed=3):
    """Sound certificate that the class of germ g is nonzero: integer rank on samples."""
    def relu(a):
        return a if a > 0 else 0
    rng = random.Random(seed)
    ns = ns or (t * (t - 1) // 2 + t + 40)
    Z = [[rng.randint(-10**4, 10**4) for _ in range(t)] for _ in range(ns)]
    v, M = g
    cols = [[z[i] for z in Z] for i in range(t)]
    cols += [[relu(z[i] - z[j]) for z in Z] for i in range(t) for j in range(i + 1, t)]
    cols += [[relu(z[i]) for z in Z] for i in range(t)]
    gc = [relu(sum(a * b for a, b in zip(v, z)) + sum(relu(z[i] - z[j]) for i, j in M)) for z in Z]
    r0 = flint.fmpz_mat(cols).rank()
    return flint.fmpz_mat(cols + [gc]).rank() > r0

N = int(sys.argv[1])
val, cols, x, y, A, data = solve(N, 'F1', 4, quiet=True)
sup = [i for i in range(len(y)) if y[i]]
print(f'N={N}: F1 optimum {val}; dual support {len(sup)} units')
nstr = {}
for (t, cp, _) in cols:
    s = math.factorial(N) // math.factorial(t)
    for a in cp:
        s //= math.factorial(a)
    nstr[(t, cp)] = s
rows = {}
for i in sup:
    key, res = data[i]
    germs = {}
    for T, (g, _) in res.items():
        germs.setdefault(len(T), set()).add(g)
    nz = {}
    for t, gs in germs.items():
        gs = sorted(gs, key=str)
        if len(sys.argv) > 2 and sys.argv[2] == 'sample':
            for g in gs:
                nz[g] = sampled_nonzero(t, g)
            continue
        _, co, _ = class_coords(t, gs)
        for g, c in zip(gs, co):
            nz[g] = any(c)
    row = {}
    for T, (g, cn) in res.items():
        if nz[g]:
            for cp, n in cn.items():
                row[(len(T), cp)] = row.get((len(T), cp), 0) + Fraction(n, nstr[(len(T), cp)])
    rows[i] = row
    print('  unit', key[0], sorted(key[1]), 'y =', y[i])
ok = True
for (t, cp, _) in cols:
    lhs = sum(y[i] * rows[i].get((t, cp), 0) for i in sup)
    flag = lhs >= 1
    ok &= flag
    print(f'  column ({t},{cp}): sum_k y_k a_k = {lhs} {"ok" if flag else "VIOLATED"}')
print('RESULT exact dual feasible:', ok, '-> tau*_F1 =', val if ok else 'not certified')
