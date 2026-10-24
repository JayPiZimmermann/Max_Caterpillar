"""Codim-2 straightness rows at (3,1)-faces (from v2/analyze + v2/faces), as in
v2/certify.py.  usage: codim2rows.py N  -> codim2_N.pkl (list of sparse rows)"""
import pickle, sys, os
from math import gcd
from core import Setup, HERE
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'v2'))
from germ2d import Germs, dot, nullspace
from germs2 import Setup as S2

N = int(sys.argv[1])
V2 = os.path.join(os.path.dirname(HERE), 'v2')
res = pickle.load(open(os.path.join(V2, f'analyze_{N}.pkl'), 'rb'))
classes = pickle.load(open(os.path.join(V2, f'faces_{N}.pkl'), 'rb'))
S = Setup(N)
G = Germs(N)


def eval_row(x):
    A = S.A
    pi = tuple(sorted(range(N), key=lambda i: (x[i], i)))
    c = A.pidx[pi]
    t = [x[pi[j]] - x[pi[j - 1]] for j in range(1, N)]
    row = {}
    for j in range(N - 1):
        if t[j]:
            row[A.var_lin(c, j)] = t[j]
    for pp in A.D[c]:
        v = sum(a * b for a, b in zip(pp, t))
        if v > 0:
            row[A.var_kink(c, pp)] = v
    return row

rows = []
for c, d in res.items():
    if not (d['k'] == 3 and d['nb'] == 1):
        continue
    for x0 in classes[c]:
        Hs, u, v, rays = G.rays2d(x0)
        Bv = 1 + max(abs(dot(h, r[0])) for h in G.hyps for r in rays)
        lin = [[r[0][i] - r[0][0] for r in rays] for i in range(1, N)]
        bumps = [[abs(dot(h, r[0])) for r in rays] for h in Hs]
        ann = nullspace(lin + bumps, len(rays))
        assert len(ann) == 1
        cvec = ann[0]
        den = 1
        for x in cvec:
            den = den * x.denominator // gcd(den, x.denominator)
        ci = [int(x * den) for x in cvec]
        base = [Bv * a for a in x0]
        row = {}
        for cc, r in zip(ci, rays):
            for k, x in eval_row([a + b for a, b in zip(base, r[0])]).items():
                row[k] = row.get(k, 0) + cc * x
        tot = sum(ci)
        for k, x in eval_row(base).items():
            row[k] = row.get(k, 0) - tot * x
        rows.append({k: x for k, x in row.items() if x})
bad = sum(1 for r in rows for v in S.V if sum(x * v.get(k, 0) for k, x in r.items()))
print(N, 'codim-2 rows', len(rows), 'violations on V (exact):', bad)
pickle.dump(rows, open(f'codim2_{N}.pkl', 'wb'))
