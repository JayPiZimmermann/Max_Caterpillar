"""Within-locality fractional covering by mixed m-th differences.
Functionals D_{a,c} f = sum_{S subset [m]} (-1)^{m-|S|} f(a + sum_{i in S} c_i e_i).
They kill every function independent of some coordinate (aux, non-full germs).
LP: max sum y_i  s.t.  sum_{i: D_i g != 0} y_i <= 1 for every full germ g,
only functionals with D_i max != 0.  Value tau <= t*_m; s_N >= tau*C(N,m)/W_m(N).
usage: packing.py m N cmax [bases]"""
import sys, itertools
import numpy as np
from scipy.optimize import linprog
from germs import localities, relabel
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs
m = int(sys.argv[1]); N = int(sys.argv[2]); cmax = int(sys.argv[3])
def isfull(g):
    h, M = g
    return all(h[t] != 0 or any(t in e for e in M) for t in range(len(h)))
G = {g for *_, g in localities(N, m)}
Gc = set()
for g in G:
    for perm in itertools.permutations(range(m)):
        Gc.add(relabel(g, perm))
full = sorted([g for g in Gc if isfull(g)], key=str)
CV = [int(x) for x in sys.argv[5].split(",")]
B = int(sys.argv[4]); bases = [(0,)+t for t in itertools.product(range(-B, B+1), repeat=m-1)]
funcs = []
for a in bases:
    for c in itertools.product(CV, repeat=m):
        pts = []
        for S in range(1 << m):
            p = list(a)
            for i in range(m):
                if S >> i & 1: p[i] += c[i]
            sign = (-1) ** (m - bin(S).count('1'))
            pts.append((sign, tuple(p)))
        dm = sum(s * max(p) for s, p in pts)
        if dm == 0: continue
        row = tuple(sum(s * vs.eval_key(g, p) for s, p in pts) != 0 for g in full)
        funcs.append((c, dm, row))
# dedupe identical rows
rows = {}
for c, dm, row in funcs:
    rows.setdefault(row, (c, dm))
R = np.array([list(r) for r in rows], dtype=float)
print(f'm={m}: full germs {len(full)}, functionals with Dmax!=0: {len(funcs)}, distinct patterns {len(R)}')
print('min #germs hit by a functional', int(R.sum(1).min()), ' germs hit by none', int((R.sum(0) == 0).sum()))
res = linprog(-np.ones(len(R)), A_ub=R.T, b_ub=np.ones(len(full)), bounds=[(0, None)] * len(R), method='highs')
print('LP tau =', -res.fun)
sup = [i for i in range(len(R)) if res.x[i] > 1e-9]
keys = list(rows.values())
for i in sup[:20]:
    print('  y=%.4f' % res.x[i], keys[i], 'hits', int(R[i].sum()))
