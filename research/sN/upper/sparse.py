#!/usr/bin/env python3
"""Sparse expansions of max_N: reweighted L1 + pruning + optional MILP.

Usage: python3 sparse.py N [rounds] [milp_seconds] [seed]
Floating point is only a search heuristic; every reported support is solved
and certified exactly (vocabulary_search.exact_expansion, all cells) and saved
to data/expansion_N_<size>.txt.
"""
import os
import sys
import time
from fractions import Fraction

import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

from system import build, certify, DATA, vs

N = int(sys.argv[1])
ROUNDS = int(sys.argv[2]) if len(sys.argv) > 2 else 8
MILP_T = float(sys.argv[3]) if len(sys.argv) > 3 else 0
SEED = int(sys.argv[4]) if len(sys.argv) > 4 else 0
rng = np.random.default_rng(SEED)

S = build(N)
units, aux, A = S['units'], S['aux'], S['A'].tocsc()
U, Aa = len(units), len(aux)
Au, Ax, b = A[:, :U], A[:, U:U + Aa], -A[:, -1].toarray().ravel()


def feasible_lp(cols, w=None):
    """min sum w|d| over d supported on cols (aux free); returns d or None."""
    cols = list(cols)
    n = len(cols)
    if w is None:
        w = np.ones(n)
    M = sp.hstack([Au[:, cols], -Au[:, cols], Ax, -Ax]).tocsr()
    c = np.concatenate([w, w, 1e-6 * np.ones(2 * Aa)])
    r = linprog(c, A_eq=M, b_eq=b, bounds=(0, None), method='highs')
    if r.status != 0:
        return None
    x = r.x
    return x[:n] - x[n:2 * n]


def exact(cols):
    supp = [units[k] for k in cols]
    return vs.exact_expansion(N, supp)


def prune(cols):
    """Greedy removal: drop units while an exact (LP) solution remains."""
    cols = list(cols)
    order = list(cols)
    rng.shuffle(order)
    for k in order:
        trial = [c for c in cols if c != k]
        if feasible_lp(trial) is not None:
            cols = trial
    return cols


best = None
t0 = time.time()
w = np.ones(U) + 0.01 * rng.random(U)
for it in range(ROUNDS):
    d = feasible_lp(range(U), w)
    supp = [k for k in range(U) if abs(d[k]) > 1e-7]
    print(f'round {it}: L1 support {len(supp)}  ({time.time() - t0:.1f}s)', flush=True)
    pr = prune(supp)
    print(f'   pruned to {len(pr)}', flush=True)
    if best is None or len(pr) < len(best):
        best = pr
    w = 1.0 / (np.abs(d) + 1e-3) * (1 + 0.1 * rng.random(U))

if MILP_T > 0:
    Mb = 50.0
    nv = 2 * U + Aa
    Aeq = sp.hstack([Au, Ax, sp.csc_matrix((A.shape[0], U))])
    I = sp.identity(U)
    Z = sp.csc_matrix((U, Aa))
    c1 = sp.hstack([I, Z, -Mb * I])
    c2 = sp.hstack([-I, Z, -Mb * I])
    cons = [LinearConstraint(Aeq, b, b), LinearConstraint(c1, -np.inf, 0),
            LinearConstraint(c2, -np.inf, 0)]
    cost = np.concatenate([np.zeros(U + Aa), np.ones(U)])
    integ = np.concatenate([np.zeros(U + Aa), np.ones(U)])
    lb = np.concatenate([-Mb * np.ones(U), -1e4 * np.ones(Aa), np.zeros(U)])
    ub = np.concatenate([Mb * np.ones(U), 1e4 * np.ones(Aa), np.ones(U)])
    r = milp(cost, constraints=cons, integrality=integ, bounds=Bounds(lb, ub),
             options={'time_limit': MILP_T, 'disp': False})
    print('MILP status', r.status, r.message, 'value', r.fun,
          'dual bound', getattr(r, 'mip_dual_bound', None), flush=True)
    if r.x is not None:
        supp = [k for k in range(U) if r.x[U + Aa + k] > 0.5 and abs(r.x[k]) > 1e-9]
        pr = prune(supp)
        print('   MILP support', len(supp), 'pruned', len(pr), flush=True)
        if len(pr) < len(best):
            best = pr

out = exact(best)
assert out is not None, 'exact solve failed on the support'
dd, ee = out
assert certify(N, dd, ee)
dd = {k: v for k, v in dd.items() if v != 0}
path = os.path.join(DATA, f'expansion_{N}_{len(dd)}_seed{SEED}.txt')
with open(path, 'w') as f:
    f.write(f'# max_{N} = sum d_k U_k + sum e_a aux_a, certified on all cells\n')
    for k, v in sorted(dd.items(), key=lambda t: (sorted(t[0][1]), t[0][0])):
        f.write(f'unit h={list(k[0])} M={sorted(k[1])} d={v}\n')
    for a, v in ee.items():
        if v != 0:
            f.write(f'aux {a} e={v}\n')
print(f'CERTIFIED support {len(dd)} -> {path}', flush=True)
