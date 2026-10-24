#!/usr/bin/env python3
"""Large neighbourhood search for sparse expansions of max_N (lns.py).

Start: L1-minimal support.  Repeat: sub-MILP (half-integer d, |2d| <= Mb,
cover cuts restricted to the columns) on current support + a random sample of
other units, time limited; keep the smallest support.  Every improvement is
solved and certified exactly on every cell and saved.

Usage: python3 lns.py N rounds sample sub_seconds seed
"""
import glob
import os
import pickle
import sys
import time

import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

import fastsys
from system import certify, DATA, vs

N, ROUNDS, SAMPLE, SUBT, SEED = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]),
                                 float(sys.argv[4]), int(sys.argv[5]))
Mb = 4.0
rng = np.random.default_rng(SEED)
S = fastsys.build(N, verbose=False)
units, aux, A = S['units'], S['aux'], S['A'].tocsc()
U, Aa = len(units), len(aux)
b = -A[:, -1].toarray().ravel()
Ax = A[:, U:U + Aa]
sets = []
for pth in glob.glob(os.path.join(DATA, f'passsets_{N}_d*.pkl')):
    sets += pickle.load(open(pth, 'rb'))


def l1(cols):
    Au = A[:, cols]
    n = len(cols)
    M = sp.hstack([Au, -Au, Ax, -Ax]).tocsr()
    c = np.concatenate([np.ones(2 * n), 1e-7 * np.ones(2 * Aa)])
    r = linprog(c, A_eq=M, b_eq=b, bounds=(0, None), method='highs')
    d = r.x[:n] - r.x[n:2 * n]
    return [cols[i] for i in range(n) if abs(d[i]) > 1e-7]


def sub_milp(cols, ub):
    n = len(cols)
    Au = A[:, cols]
    Aeq = sp.hstack([Au, Ax, sp.csc_matrix((A.shape[0], n))])
    I = sp.identity(n)
    Z = sp.csc_matrix((n, Aa))
    cons = [LinearConstraint(Aeq, 2 * b, 2 * b),
            LinearConstraint(sp.hstack([I, Z, -Mb * I]), -np.inf, 0),
            LinearConstraint(sp.hstack([-I, Z, -Mb * I]), -np.inf, 0)]
    pos = {k: i for i, k in enumerate(cols)}
    rows = [[pos[k] for k in s if k in pos] for s in sets]
    if any(not r for r in rows):
        return None
    Cm = sp.lil_matrix((len(rows), 2 * n + Aa))
    for r, s in enumerate(rows):
        for i in s:
            Cm[r, n + Aa + i] = 1
    cons.append(LinearConstraint(Cm.tocsr(), 1, np.inf))
    cons.append(LinearConstraint(np.concatenate([np.zeros(n + Aa), np.ones(n)])[None, :],
                                 -np.inf, ub - 1))
    cost = np.concatenate([np.zeros(n + Aa), np.ones(n)])
    integ = np.concatenate([np.ones(n), np.zeros(Aa), np.ones(n)])
    lb = np.concatenate([-Mb * np.ones(n), -1e4 * np.ones(Aa), np.zeros(n)])
    ubd = np.concatenate([Mb * np.ones(n), 1e4 * np.ones(Aa), np.ones(n)])
    r = milp(cost, constraints=cons, integrality=integ, bounds=Bounds(lb, ubd),
             options={'time_limit': SUBT})
    if r.x is None:
        return None
    return [cols[i] for i in range(n) if r.x[n + Aa + i] > 0.5]


def save(supp, tag):
    out = vs.exact_expansion(N, [units[k] for k in supp])
    if out is None:
        return None
    dd, ee = out
    assert certify(N, dd, ee)
    dd = {k: v for k, v in dd.items() if v != 0}
    path = os.path.join(DATA, f'expansion_{N}_{len(dd)}_{tag}.txt')
    with open(path, 'w') as f:
        f.write(f'# max_{N} = sum d_k U_k + sum e_a aux_a, certified exactly on all cells '
                f'(lns.py {" ".join(sys.argv[1:])})\n')
        for k, v in sorted(dd.items(), key=lambda t: (sorted(t[0][1]), t[0][0])):
            f.write(f'unit h={list(k[0])} M={sorted(k[1])} d={v}\n')
        for a, v in ee.items():
            if v != 0:
                f.write(f'aux {a} e={v}\n')
    return len(dd), path


t0 = time.time()
init = sys.argv[6] if len(sys.argv) > 6 else None
if init:
    keys = []
    for line in open(init):
        if line.startswith('unit'):
            h = eval(line.split('h=')[1].split(' M=')[0])
            M = eval(line.split('M=')[1].split(' d=')[0])
            keys.append((tuple(h), frozenset(M)))
    kidx = {k: i for i, k in enumerate(units)}
    cur = [kidx[k] for k in keys]
else:
    cur = l1(list(range(U)))
print(f'initial support {len(cur)} ({time.time() - t0:.0f}s)', flush=True)
for it in range(ROUNDS):
    others = [k for k in range(U) if k not in set(cur)]
    samp = list(rng.choice(others, size=min(SAMPLE, len(others)), replace=False))
    cols = sorted(set(cur) | set(int(s) for s in samp))
    new = sub_milp(cols, len(cur))
    if new is not None and len(new) < len(cur):
        res = save(new, f'lns_s{SEED}')
        if res is not None:
            cur = new
            print(f'round {it}: support {len(cur)} certified {res} ({time.time() - t0:.0f}s)',
                  flush=True)
print('final', len(cur), flush=True)
