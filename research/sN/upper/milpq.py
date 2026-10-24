#!/usr/bin/env python3
"""MILP with half-integer coefficients d_k = D_k/2, |D_k| <= Mb (milpq.py).
Variant of milp.py; the found support is re-solved and certified exactly.

min sum z_k  s.t. cell system exact equalities, |d_k| <= Mb z_k, z binary.
Optional: restrict to a candidate unit list (indices file), or fix an upper
bound on the support.  The MILP is floating point (a search heuristic and a
MEASURED dual bound valid only under |d_k| <= Mb); the support found is
re-solved exactly and certified on every cell, then saved.

Usage: python3 milp.py N seconds [Mb] [builder: f|s]
"""
import os
import sys
import time

import numpy as np
import scipy.sparse as sp
from scipy.optimize import milp, LinearConstraint, Bounds

N = int(sys.argv[1])
TL = float(sys.argv[2])
Mb = float(sys.argv[3]) if len(sys.argv) > 3 else 4.0  # bound on 2*d_k
import fastsys  # noqa: E402
from system import certify, DATA, vs  # noqa: E402

S = fastsys.build(N)
units, aux, A = S['units'], S['aux'], S['A'].tocsc()
U, Aa = len(units), len(aux)
Au, Ax, b = A[:, :U], A[:, U:U + Aa], -A[:, -1].toarray().ravel()
t0 = time.time()
Aeq = sp.hstack([Au, Ax, sp.csc_matrix((A.shape[0], U))])
I = sp.identity(U)
Z = sp.csc_matrix((U, Aa))
cons = [LinearConstraint(Aeq, 2 * b, 2 * b),
        LinearConstraint(sp.hstack([I, Z, -Mb * I]), -np.inf, 0),
        LinearConstraint(sp.hstack([-I, Z, -Mb * I]), -np.inf, 0)]
cost = np.concatenate([np.zeros(U + Aa), np.ones(U)])
integ = np.concatenate([np.ones(U), np.zeros(Aa), np.ones(U)])  # D_k = 2 d_k integer
lb = np.concatenate([-Mb * np.ones(U), -1e4 * np.ones(Aa), np.zeros(U)])
ub = np.concatenate([Mb * np.ones(U), 1e4 * np.ones(Aa), np.ones(U)])
r = milp(cost, constraints=cons, integrality=integ, bounds=Bounds(lb, ub),
         options={'time_limit': TL, 'disp': True})
print('MILP status', r.status, r.message, 'value', r.fun,
      'dual bound', getattr(r, 'mip_dual_bound', None),
      f'{time.time() - t0:.0f}s', flush=True)
if r.x is not None:
    supp = [units[k] for k in range(U) if r.x[U + Aa + k] > 0.5]
    out = vs.exact_expansion(N, supp)
    assert out is not None
    dd, ee = out
    assert certify(N, dd, ee)
    dd = {k: v for k, v in dd.items() if v != 0}
    path = os.path.join(DATA, f'expansion_{N}_{len(dd)}_milpq.txt')
    with open(path, 'w') as f:
        f.write(f'# max_{N} = sum d_k U_k + sum e_a aux_a, certified on all cells\n')
        for k, v in sorted(dd.items(), key=lambda t: (sorted(t[0][1]), t[0][0])):
            f.write(f'unit h={list(k[0])} M={sorted(k[1])} d={v}\n')
        for a, v in ee.items():
            if v != 0:
                f.write(f'aux {a} e={v}\n')
    print(f'CERTIFIED support {len(dd)} -> {path}', flush=True)
