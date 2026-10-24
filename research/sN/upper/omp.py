#!/usr/bin/env python3
"""Greedy (OMP) + swap local search for sparse expansions of max_N.

The auxiliary columns are always in the model.  For a support S the residual
r(S) = min || A_S d + A_aux e - b ||_2 is computed in floating point.  OMP adds
the unit that best reduces the residual until it vanishes; then the search
tries to shrink: remove a unit, re-add by OMP until feasible, accept if the
size does not grow (random tie-breaking, restarts).  Any support with residual
< 1e-9 is solved and certified exactly on every cell and saved.

Usage: python3 omp.py N restarts seed [iters]
"""
import os
import sys
import time

import numpy as np

import fastsys
from system import certify, DATA, vs

N = int(sys.argv[1])
RESTARTS = int(sys.argv[2])
SEED = int(sys.argv[3])
ITERS = int(sys.argv[4]) if len(sys.argv) > 4 else 200
rng = np.random.default_rng(SEED)

S = fastsys.build(N, verbose=False)
units, aux, A = S['units'], S['aux'], S['A'].tocsc()
U, Aa = len(units), len(aux)
b = -A[:, -1].toarray().ravel()
Au = A[:, :U].tocsc()
Ax = A[:, U:U + Aa].toarray()
Qx, _ = np.linalg.qr(Ax)
Qx = Qx[:, np.abs(np.linalg.qr(Ax)[1].diagonal()) > 1e-9]
colnorm2 = np.asarray(Au.multiply(Au).sum(0)).ravel()
TOL = 1e-9


def basis(supp):
    cols = np.hstack([Qx, Au[:, supp].toarray()]) if supp else Qx
    Q, R = np.linalg.qr(cols)
    keep = np.abs(R.diagonal()) > 1e-9 * max(1, np.abs(R.diagonal()).max())
    return Q[:, keep]


def residual(Q):
    return b - Q @ (Q.T @ b)


def omp_fill(supp, noise=0.0):
    supp = list(supp)
    while True:
        Q = basis(supp)
        r = residual(Q)
        if r @ r < TOL:
            return supp
        # score_c = (c . r)^2 / ||c - Q Q^T c||^2
        cr = Au.T @ r
        QtC = (Au.T @ Q)             # U x k
        proj = colnorm2 - (QtC ** 2).sum(1)
        score = np.where(proj > 1e-9, cr ** 2 / np.maximum(proj, 1e-12), 0)
        if noise:
            score = score * (1 + noise * rng.random(U))
        score[supp] = -1
        supp.append(int(np.argmax(score)))


def save(supp):
    out = vs.exact_expansion(N, [units[k] for k in supp])
    if out is None:
        return None
    dd, ee = out
    assert certify(N, dd, ee)
    dd = {k: v for k, v in dd.items() if v != 0}
    path = os.path.join(DATA, f'expansion_{N}_{len(dd)}_omp.txt')
    if not os.path.exists(path):
        with open(path, 'w') as f:
            f.write(f'# max_{N} = sum d_k U_k + sum e_a aux_a, certified exactly on all cells '
                    f'(omp.py N={N} seed={SEED})\n')
            for k, v in sorted(dd.items(), key=lambda t: (sorted(t[0][1]), t[0][0])):
                f.write(f'unit h={list(k[0])} M={sorted(k[1])} d={v}\n')
            for a, v in ee.items():
                if v != 0:
                    f.write(f'aux {a} e={v}\n')
    return len(dd), path


def prune(supp):
    supp = list(supp)
    changed = True
    while changed:
        changed = False
        for k in list(supp):
            t = [c for c in supp if c != k]
            r = residual(basis(t))
            if r @ r < TOL:
                supp = t
                changed = True
    return supp


best = None
t0 = time.time()
for rs in range(RESTARTS):
    cur = prune(omp_fill([], noise=0.0 if rs == 0 else 0.5))
    for it in range(ITERS):
        drop = rng.choice(len(cur), size=min(len(cur), rng.integers(1, 4)), replace=False)
        trial = [c for i, c in enumerate(cur) if i not in set(drop)]
        trial = prune(omp_fill(trial, noise=0.3))
        if len(trial) <= len(cur):
            cur = trial
        if best is None or len(cur) < len(best):
            best = list(cur)
            print(f'restart {rs} it {it}: support {len(best)} ({time.time() - t0:.0f}s)', flush=True)
    print(f'restart {rs} done: current {len(cur)}, best {len(best)}', flush=True)
res = save(best)
print('CERTIFIED', res, flush=True)
