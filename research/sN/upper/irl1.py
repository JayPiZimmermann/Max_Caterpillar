#!/usr/bin/env python3
"""Iteratively reweighted L1 (Candes-Wakin-Boyd) for sparse expansions of max_N.
Floating point heuristic; the final support is solved and certified exactly.
Usage: python3 irl1.py N iters seed [apex-restriction e.g. 012]"""
import os, sys, time
import numpy as np, scipy.sparse as sp
from scipy.optimize import linprog
import fastsys
from system import certify, DATA, vs
N, IT, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = np.random.default_rng(SEED)
S = fastsys.build(N, verbose=False)
units, aux, A = S['units'], S['aux'], S['A'].tocsc()
U, Aa = len(units), len(aux)
b = -A[:, -1].toarray().ravel()
cols = list(range(U))
if len(sys.argv) > 4:
    allowed = set(int(c) for c in sys.argv[4])
    def apexes(k):
        h, M = k; used = {i for p in M for i in p}
        return {o for o in range(N) if h[o] == -1 and o not in used}
    cols = [i for i in cols if apexes(units[i]) & allowed]
Au, Ax = A[:, cols], A[:, U:U + Aa]
n = len(cols)
Mx = sp.hstack([Au, -Au, Ax, -Ax]).tocsr()
w = np.ones(n) * (1 + 0.05 * rng.random(n))
eps = 1.0
best = None
t0 = time.time()
for it in range(IT):
    c = np.concatenate([w, w, 1e-7 * np.ones(2 * Aa)])
    r = linprog(c, A_eq=Mx, b_eq=b, bounds=(0, None), method='highs')
    d = r.x[:n] - r.x[n:2 * n]
    supp = [cols[i] for i in range(n) if abs(d[i]) > 1e-6]
    print(f'it {it}: support {len(supp)} eps {eps:.3g} ({time.time() - t0:.0f}s)', flush=True)
    if best is None or len(supp) < len(best):
        best = supp
    w = 1.0 / (np.abs(d) + eps) * (1 + 0.05 * rng.random(n))
    eps = max(eps * 0.5, 1e-3)
out = vs.exact_expansion(N, [units[k] for k in best])
assert out is not None
dd, ee = out
assert certify(N, dd, ee)
dd = {k: v for k, v in dd.items() if v != 0}
path = os.path.join(DATA, f'expansion_{N}_{len(dd)}_irl1_s{SEED}.txt')
with open(path, 'w') as f:
    f.write(f'# max_{N} = sum d_k U_k + sum e_a aux_a, certified exactly on all cells (irl1.py {" ".join(sys.argv[1:])})\n')
    for k, v in sorted(dd.items(), key=lambda t: (sorted(t[0][1]), t[0][0])):
        f.write(f'unit h={list(k[0])} M={sorted(k[1])} d={v}\n')
    for a, v in ee.items():
        if v != 0:
            f.write(f'aux {a} e={v}\n')
print('CERTIFIED', len(dd), path, flush=True)
