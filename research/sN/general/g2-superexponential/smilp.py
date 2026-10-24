"""Fewest non-auxiliary keys of K_0(k) in an exact expansion  target = sum d_u U_u + R, R in A_k,
for target = max_k or min_k (point evaluations, float MILP with big-M, exact mod-p recheck).
Usage: python smilp.py k npoints seed target(max|min) timelimit [bigM]
"""
import sys, time
import numpy as np
import highspy
from mixed import *

k, m, seed, target, tl = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], float(sys.argv[5])
BIG = float(sys.argv[6]) if len(sys.argv) > 6 else 50.0
keys = load_keys(k)
rng = np.random.default_rng(seed)
f = (lambda X: X.max(axis=1)) if target == 'max' else (lambda X: X.min(axis=1))


def auxcols(X):
    a = []
    for i in range(k):
        a.append(np.maximum(X[:, i], 0)); a.append(np.maximum(-X[:, i], 0))
    for i in range(k):
        for j in range(i + 1, k):
            a.append(np.maximum(X[:, i] - X[:, j], 0))
    return np.array(a).T


X = rng.integers(-40, 41, size=(m, k))
A = eval_keys(keys, X).astype(float)
F = auxcols(X).astype(float)
b = f(X).astype(float)
inspan = rank_modp(np.column_stack([A, F, b])) == rank_modp(np.column_stack([A, F]))
print('k', k, target, 'keys', len(keys), 'target in span', inspan, flush=True)
Z = np.column_stack([A, F, b])
U_, s_, _ = np.linalg.svd(Z, full_matrices=False)
r = int((s_ > 1e-9 * s_[0]).sum())
Bm = U_[:, :r]
A2, F2, b2 = Bm.T @ A, Bm.T @ F, Bm.T @ b
nf, na = A2.shape[1], F2.shape[1]
h = highspy.Highs()
h.setOptionValue('output_flag', False)
h.setOptionValue('time_limit', tl)
inf = highspy.kHighsInf
for _ in range(nf):
    h.addVar(-BIG, BIG)
for _ in range(na):
    h.addVar(-inf, inf)
for _ in range(nf):
    h.addVar(0, 1)
for j in range(nf):
    h.changeColCost(nf + na + j, 1.0)
    h.changeColIntegrality(nf + na + j, highspy.HighsVarType.kInteger)
for i in range(r):
    h.addRow(b2[i] - 1e-7, b2[i] + 1e-7, nf + na, list(range(nf + na)), list(A2[i]) + list(F2[i]))
for j in range(nf):
    h.addRow(-inf, 0, 2, [j, nf + na + j], [1.0, -BIG])
    h.addRow(0, inf, 2, [j, nf + na + j], [1.0, BIG])
t0 = time.time()
h.run()
info = h.getInfo()
sol = np.array(h.getSolution().col_value)
chosen = [j for j in range(nf) if sol[nf + na + j] > 0.5]
X2 = rng.integers(-60, 61, size=(3 * m, k))
Fe = np.column_stack([eval_keys([keys[c] for c in chosen], X2), auxcols(X2)])
ok = rank_modp(np.column_stack([Fe, f(X2)])) == rank_modp(Fe)
print('status', h.modelStatusToString(h.getModelStatus()), 'obj', round(info.objective_function_value, 3),
      'bound', round(info.mip_dual_bound, 3), 'secs', round(time.time() - t0, 1), 'chosen', len(chosen), 'exact', ok)
for c in chosen:
    print('   ', keys[c][0], sorted(keys[c][1]), 'd=%.4f' % sol[c])
