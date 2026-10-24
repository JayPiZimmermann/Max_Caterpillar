import sys, runpy
import numpy as np
from fractions import Fraction as Fr
from math import comb
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix, hstack
from linalg import solve
src = open('gadget_lp.py').read().split('nv = len(types)')[0]
g = {'__name__': 'x'}; exec(src, g)
types, cross, top, m = g['types'], g['cross'], g['top'], g['m']
nv = len(types); inv = {v: t for t, v in types.items()}
rows = list(cross.values()) + [top]
M = lil_matrix((len(rows), nv))
for i, e in enumerate(rows):
    for v, c in e.items(): M[i, v] = float(c)
M = csr_matrix(M); b = np.zeros(len(rows)); b[-1] = 1
cost = np.array([comb(m, inv[v][3]) for v in range(nv)], dtype=float)
wts = cost.copy(); best = None
for it in range(5):
    res = linprog(np.concatenate([wts, wts]), A_eq=hstack([M, -M]), b_eq=b, bounds=(0, None), method='highs')
    x = res.x[:nv] - res.x[nv:]; supp = [v for v in range(nv) if abs(x[v]) > 1e-9]
    tot = sum(cost[v] for v in supp); print('iter', it, 'types', len(supp), 'neurons', tot, flush=True)
    if best is None or tot < best[0]: best = (tot, supp)
    wts = cost / (np.abs(x) + 1e-5)
tot, supp = best
sub = [{v: e[v] for v in e if v in supp} for e in rows]
ok, sol, _, _ = solve(sub, [0] * (len(rows) - 1) + [1], nv)
print('exact', ok, 'neurons', tot)
for v in supp: print(inv[v], sol.get(v, 0))
