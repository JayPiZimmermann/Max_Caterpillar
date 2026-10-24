"""Upper bounds for tau_k by iteratively reweighted L1 (LP, HiGHS) on mixed-difference vectors,
with exact mod-p recheck of the final support and greedy column pruning.
Usage: python tau_irl1.py k nsamples seed iters
"""
import sys
import numpy as np
import highspy
from mixed import *

k, m, seed, iters = map(int, sys.argv[1:5])
keys = load_keys(k)
rng = np.random.default_rng(seed)
Y = rng.integers(-6, 7, size=(m, k)) + rng.integers(-1000, 1000, size=(m, 1))
D = rng.integers(1, 12, size=(m, k)) * rng.choice([-1, 1], size=(m, k))
Mu = mixed_rows(lambda X: eval_keys(keys, X), Y, D)
Mmax = mixed_rows(lambda X: X.max(axis=1)[:, None], Y, D)[:, 0]
full = [c for c in range(len(keys)) if np.any(Mu[:, c])]
A = Mu[:, full].astype(float)
U_, s_, _ = np.linalg.svd(np.column_stack([A, Mmax]), full_matrices=False)
r = int((s_ > 1e-9 * s_[0]).sum())
A2, b2 = U_[:, :r].T @ A, U_[:, :r].T @ Mmax
n = A2.shape[1]
print('k', k, 'rank', r, 'full-support keys', n, flush=True)


def l1(wts, cols):
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    nc = len(cols)
    for j in range(nc):
        h.addVar(0, highspy.kHighsInf); h.changeColCost(j, wts[j])
    for j in range(nc):
        h.addVar(0, highspy.kHighsInf); h.changeColCost(nc + j, wts[j])
    for i in range(r):
        h.addRow(b2[i], b2[i], 2 * nc, list(range(2 * nc)), list(A2[i, cols]) + list(-A2[i, cols]))
    h.run()
    x = np.array(h.getSolution().col_value)
    return x[:nc] - x[nc:], h.modelStatusToString(h.getModelStatus())


cols = np.arange(n)
w = np.ones(n)
best = None
for it in range(iters):
    x, st = l1(w, cols)
    supp = np.nonzero(np.abs(x) > 1e-7)[0]
    w = 1.0 / (np.abs(x) + 1e-3)
    if best is None or len(supp) < len(best):
        best = cols[supp]
    print('iter', it, st, 'support', len(supp), flush=True)
# greedy pruning with exact check
S = [full[j] for j in best]
def ok(S):
    B = Mu[:, S]
    return rank_modp(np.column_stack([B, Mmax])) == rank_modp(B)
assert ok(S)
i = 0
while i < len(S):
    T = S[:i] + S[i + 1:]
    if ok(T):
        S = T
    else:
        i += 1
print('exact support after pruning', len(S))
for c in S:
    print('   ', keys[c][0], sorted(keys[c][1]))
