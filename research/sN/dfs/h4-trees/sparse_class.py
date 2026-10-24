#!/usr/bin/env python3
"""Upper bound on s_N for a tree class: L1 LP on random integer points, then
greedy deletion with mod-p rank tests, then exact verification of the final
expansion on every cell (vocabulary_search.exact_expansion).  (branch h4-trees)
Usage: python sparse_class.py N mode seed"""
import sys, random
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs
import treeclass as tc
N = int(sys.argv[1]); mode = sys.argv[2]; seed = int(sys.argv[3])
K = sorted(k for k in tc.vocabulary(N, mode) if not tc.is_aux(k) and (any(k[0]) or k[1]))
aux = vs.aux_functions(N)
rng = random.Random(seed)
npts = 3 * (len(K) + len(aux)) + 200
pts = [[rng.randint(-40, 40) for _ in range(N)] for _ in range(npts)]
EK = np.array([[vs.eval_key(k, x) for k in K] for x in pts], dtype=float)
EA = np.array([[vs.eval_aux(a, x) for a in aux] for x in pts], dtype=float)
b = np.array([max(x) for x in pts], dtype=float)
nK, nA = len(K), len(aux)
w = np.array([rng.uniform(0.9, 1.1) for _ in range(nK)])
# variables d+ (nK), d- (nK), e (nA, free)
c = np.concatenate([w, w, np.zeros(nA)])
Aeq = np.hstack([EK, -EK, EA])
bounds = [(0, None)] * (2 * nK) + [(None, None)] * nA
res = linprog(c, A_eq=Aeq, b_eq=b, bounds=bounds, method='highs')
print('LP status', res.status, res.message[:60], flush=True)
d = res.x[:nK] - res.x[nK:2 * nK]
supp = [i for i in range(nK) if abs(d[i]) > 1e-7]
print(f'N={N} mode={mode}: |K|={nK}, LP support {len(supp)}', flush=True)

def in_span(S):
    cols = [EK[:, i] for i in S] + [EA[:, j] for j in range(nA)]
    M = np.array(cols).T.astype(np.int64)
    r0 = len(vs.rref_mod_p(M)[1])
    r1 = len(vs.rref_mod_p(np.hstack([M, b.astype(np.int64)[:, None]]))[1])
    return r0 == r1

assert in_span(supp)
order = sorted(supp, key=lambda i: abs(d[i]))
cur = list(supp)
for i in order:
    trial = [j for j in cur if j != i]
    if in_span(trial):
        cur = trial
print(f'greedy minimal support {len(cur)}', flush=True)
units = [K[i] for i in cur]
res = vs.exact_expansion(N, units)
assert res is not None, 'exact verification failed'
dd, ee = res
print(f'EXACT: max_{N} = sum of {sum(1 for v in dd.values() if v)} {mode}-units + aux (verified on all cells)')
for k, v in dd.items():
    if v: print('   ', k[0], sorted(k[1]), v)
