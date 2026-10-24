#!/usr/bin/env python3
"""Minimum hitting set of tie-functional pass sets (a lower bound on s_N).
Usage: python3 hitset.py N depth"""
import sys, pickle, os, time
import numpy as np, scipy.sparse as sp
from scipy.optimize import milp, LinearConstraint, Bounds
import fastsys, cuts
N, depth = int(sys.argv[1]), int(sys.argv[2])
S = fastsys.build(N, verbose=False); units = S['units']
path = os.path.join(fastsys.DATA, f'passsets_{N}_d{depth}.pkl')
if os.path.exists(path):
    ms = pickle.load(open(path, 'rb'))
else:
    t = time.time()
    pts = cuts.tie_points(N, svals=(0, 1, -1), depth=depth)
    ms = cuts.minimal_sets(cuts.pass_sets(N, units, pts))
    pickle.dump(ms, open(path, 'wb'))
    print('pass sets', len(ms), f'{time.time()-t:.0f}s')
used = sorted(set().union(*ms))
idx = {k: i for i, k in enumerate(used)}
rows = [[idx[k] for k in s] for s in ms]
A = sp.lil_matrix((len(rows), len(used)))
for r, s in enumerate(rows):
    for j in s: A[r, j] = 1
res = milp(np.ones(len(used)), constraints=[LinearConstraint(A.tocsr(), 1, np.inf)],
           integrality=np.ones(len(used)), bounds=Bounds(0, 1), options={'time_limit': 600})
print('N', N, 'sets', len(ms), 'units involved', len(used), 'min hitting set', res.fun, res.message)
