"""MILP for tau_k (fewest units matching max_k modulo lower-support functions) and for
t_k (same, but the lower-support remainder must lie in the span of lower-support keys and
auxiliary functions; checked on point evaluations instead of mixed differences).
Float MILP (HiGHS) with big-M; every reported solution is re-verified exactly mod p.
Usage: python tau_milp.py k nsamples seed mode(tau|t) timelimit
"""
import sys, time
import numpy as np
import highspy
from mixed import *

k, m, seed, mode, tl = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], float(sys.argv[5])
TARGET = sys.argv[6] if len(sys.argv) > 6 else 'max'
tgt = (lambda X: X.max(axis=1)) if TARGET == 'max' else (lambda X: X.min(axis=1))
keys = load_keys(k)
rng = np.random.default_rng(seed)
Y = rng.integers(-6, 7, size=(m, k)) + rng.integers(-1000, 1000, size=(m, 1))
D = rng.integers(1, 12, size=(m, k)) * rng.choice([-1, 1], size=(m, k))
Mu = mixed_rows(lambda X: eval_keys(keys, X), Y, D)
Mmax = mixed_rows(lambda X: X.max(axis=1)[:, None], Y, D)[:, 0]
full = [c for c in range(len(keys)) if np.any(Mu[:, c])]
low = [c for c in range(len(keys)) if not np.any(Mu[:, c])]
print('k', k, 'keys', len(keys), 'full-support', len(full), 'lower', len(low), flush=True)

if mode == 'tau':
    A = Mu[:, full].astype(float)
    b = Mmax.astype(float)
    free = np.zeros((m, 0))
else:
    # point evaluations: max = sum_full d U + sum_low e U + aux
    X = rng.integers(-40, 41, size=(4 * m, k))
    Ev = eval_keys(keys, X).astype(float)
    aux = []
    for i in range(k):
        aux.append(np.maximum(X[:, i], 0)); aux.append(np.maximum(-X[:, i], 0))
    for i in range(k):
        for j in range(i + 1, k):
            aux.append(np.maximum(X[:, i] - X[:, j], 0))
    A = Ev[:, full]
    free = np.column_stack([Ev[:, low]] + [np.array(aux, dtype=float).T])
    b = X.max(axis=1).astype(float)
# compress rows
Z = np.column_stack([A, free, b])
U_, s_, _ = np.linalg.svd(Z, full_matrices=False)
r = int((s_ > 1e-8 * s_[0]).sum())
Bm = U_[:, :r]
A2, F2, b2 = Bm.T @ A, Bm.T @ free, Bm.T @ b
nf, nfree = A2.shape[1], F2.shape[1]
BIG = 50.0
h = highspy.Highs()
h.setOptionValue('output_flag', False)
h.setOptionValue('time_limit', tl)
inf = highspy.kHighsInf
# variables: d (nf), e (nfree), z (nf binary)
for _ in range(nf):
    h.addVar(-BIG, BIG)
for _ in range(nfree):
    h.addVar(-inf, inf)
for _ in range(nf):
    h.addVar(0, 1)
for j in range(nf):
    h.changeColCost(nf + nfree + j, 1.0)
    h.changeColIntegrality(nf + nfree + j, highspy.HighsVarType.kInteger)
for i in range(r):
    idx = list(range(nf + nfree))
    vals = list(A2[i]) + list(F2[i])
    h.addRow(b2[i] - 1e-7, b2[i] + 1e-7, len(idx), idx, vals)
for j in range(nf):  # -BIG z <= d <= BIG z
    h.addRow(-inf, 0, 2, [j, nf + nfree + j], [1.0, -BIG])
    h.addRow(0, inf, 2, [j, nf + nfree + j], [1.0, BIG])
t0 = time.time()
h.run()
info = h.getInfo()
sol = np.array(h.getSolution().col_value)
zs = sol[nf + nfree:]
chosen = [full[j] for j in range(nf) if zs[j] > 0.5]
print('status', h.modelStatusToString(h.getModelStatus()), 'obj', info.objective_function_value,
      'bound', info.mip_dual_bound, 'secs', round(time.time() - t0, 1), flush=True)
# exact verification
if mode == 'tau':
    ok = rank_modp(np.column_stack([Mu[:, chosen], Mmax])) == rank_modp(Mu[:, chosen])
else:
    X = rng.integers(-60, 61, size=(6 * m, k))
    Ev = eval_keys(keys, X)
    aux = []
    for i in range(k):
        aux.append(np.maximum(X[:, i], 0)); aux.append(np.maximum(-X[:, i], 0))
    for i in range(k):
        for j in range(i + 1, k):
            aux.append(np.maximum(X[:, i] - X[:, j], 0))
    Fe = np.column_stack([Ev[:, chosen], Ev[:, low], np.array(aux).T])
    ok = rank_modp(np.column_stack([Fe, X.max(axis=1)])) == rank_modp(Fe)
print('chosen', len(chosen), 'exact-verified', ok)
for c in chosen:
    print('   ', keys[c][0], sorted(keys[c][1]))
