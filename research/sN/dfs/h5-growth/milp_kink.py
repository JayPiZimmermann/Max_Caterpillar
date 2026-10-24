"""Heuristic upper bounds on s_N: big-M MILP on the exact kink formulation.
Any solution found is re-solved exactly on its support (solve.System) and
independently certified on all fine cells (vocabulary_search.exact_expansion).
The big-M bound makes the MILP *not* a lower-bound instrument.
usage: python milp_kink.py N bigM time_limit [threads] [seed]
"""
import pickle
import sys
import time

import highspy
import numpy as np

from solve import System

N, BM, TL = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
TH = int(sys.argv[4]) if len(sys.argv) > 4 else 4
SEED = int(sys.argv[5]) if len(sys.argv) > 5 else 0
S = System(N)
n = S.n
h = highspy.Highs()
h.setOptionValue('time_limit', TL)
h.setOptionValue('threads', TH)
h.setOptionValue('random_seed', SEED)
h.setOptionValue('mip_rel_gap', 0.0)
inf = highspy.kHighsInf
# columns: d_0..d_{n-1}, z_0..z_{n-1}
for u in range(n):
    h.addVar(-BM, BM)
for u in range(n):
    h.addVar(0, 1)
h.changeColsIntegrality(n, np.arange(n, 2 * n, dtype=np.int32),
                        np.array([highspy.HighsVarType.kInteger] * n))
h.changeColsCost(n, np.arange(n, 2 * n, dtype=np.int32), np.ones(n))
for g in S.gkeys:
    grp = S.groups[g]
    idx = np.array(list(grp), dtype=np.int32)
    val = np.array([grp[u] for u in grp], dtype=float)
    h.addRow(0, 0, len(idx), idx, val)
for s in range(S.Dm.shape[0]):
    idx = np.nonzero(S.Dm[s])[0].astype(np.int32)
    val = S.Dm[s, idx].astype(float)
    t = float(S.tD[s])
    h.addRow(t, t, len(idx), idx, val)
for u in range(n):
    h.addRow(-inf, 0, 2, np.array([u, n + u], dtype=np.int32), np.array([1.0, -BM]))
    h.addRow(-inf, 0, 2, np.array([u, n + u], dtype=np.int32), np.array([-1.0, -BM]))
t0 = time.time()
h.run()
info = h.getInfo()
print('status', h.modelStatusToString(h.getModelStatus()), 'obj', info.objective_function_value,
      'bound', info.mip_dual_bound, 't', round(time.time() - t0), flush=True)
sol = h.getSolution().col_value
K = [u for u in range(n) if sol[n + u] > 0.5 and abs(sol[u]) > 1e-9]
print('support', len(K), flush=True)
ex = S.solve(K)
print('exact feasible on support:', ex is not None, flush=True)
if ex is not None:
    K2 = [u for u in K if ex.get(u, 0) != 0]
    pickle.dump({'N': N, 'K': [S.U[u] for u in K2], 'd': {S.U[u]: ex[u] for u in K2}},
                open(f'data/milp_{N}_{int(BM)}_{SEED}.pkl', 'wb'))
    print('exact support', len(K2))
