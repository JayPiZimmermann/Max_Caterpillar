"""Certify V^TI_N = Lambda_N for N = 4, 5 (rank argument mod p).

Lambda_N := {f in W_N : germ of f is straight at every codim-2 face of the
global fan through which exactly 3 hyperplanes pass, one of them braid}.
(W_N already forces straightness at faces with no braid hyperplane.)
V <= Lambda exactly (V-germs at these faces are straight: analyze.py, exact).
dim Lambda <= nvars - rank_p(C ; cond)  and  dim V >= rank_p(V vectors).
Equality of the two numbers certifies V = Lambda.
usage: certify.py N [p]"""
import pickle, sys, time
from fractions import Fraction
from math import gcd
import numpy as np
sys.path.insert(0, '..')
from germs2 import Setup, PR, to_nmod
from germ2d import Germs, dot, nullspace
import flint

N = int(sys.argv[1]); p = int(sys.argv[2]) if len(sys.argv) > 2 else PR
t0 = time.time()
S = Setup(N, p)
G = Germs(N)
res = pickle.load(open(f'analyze_{N}.pkl', 'rb'))
classes = pickle.load(open(f'faces_{N}.pkl', 'rb'))
C = S.A.constraints()
rows = [dict(r) for r in C]
nC = len(rows)
ncond = 0
types = set()
for c, d in res.items():
    if not (d['k'] == 3 and d['nb'] == 1):
        continue
    for x0 in classes[c]:
        Hs, u, v, rays = G.rays2d(x0)
        assert len(Hs) == 3
        types.add(tuple(sorted(tuple(sorted(map(abs, h))) for h in Hs)))
        Bv = 1 + max(abs(dot(h, r[0])) for h in G.hyps for r in rays)
        # functional on the 6 ray values killing linear functions and straight bumps
        lin = [[r[0][i] - r[0][0] for r in rays] for i in range(1, N)]
        bumps = []
        for h in Hs:
            bumps.append([abs(dot(h, r[0])) for r in rays])
        ann = nullspace(lin + bumps, len(rays))
        assert len(ann) == 1, len(ann)
        cvec = ann[0]
        den = 1
        for x in cvec:
            den = den * x.denominator // gcd(den, x.denominator)
        ci = [int(x * den) for x in cvec]
        base = [Bv * a for a in x0]
        row = {}
        for cc, r in zip(ci, rays):
            for k, x in S.eval_row([a + b for a, b in zip(base, r[0])]).items():
                row[k] = row.get(k, 0) + cc * x
        tot = sum(ci)
        for k, x in S.eval_row(base).items():
            row[k] = row.get(k, 0) - tot * x
        rows.append({k: x for k, x in row.items() if x})
        ncond += 1
bad = 0
for r in rows[nC:]:
    for v in S.Vrows:
        if sum(x * v.get(k, 0) for k, x in r.items()) != 0:
            bad += 1
print('exact integer check: condition rows violated by V generators:', bad, flush=True)
print('conditions', ncond, 'types', types, f'{time.time()-t0:.1f}s', flush=True)
M = flint.nmod_mat(len(rows), S.A.nvars, p)
for i, r in enumerate(rows):
    for k, x in r.items():
        M[i, k] = x % p
Mc = flint.nmod_mat(nC, S.A.nvars, p)
for i, r in enumerate(C):
    for k, x in r.items():
        Mc[i, k] = x % p
rC = Mc.rank(); rAll = M.rank()
rV = to_nmod(S.Vmat, p).rank()
print(f'N={N} nvars={S.A.nvars} dimW<= {S.A.nvars - rC}  dimLambda<= {S.A.nvars - rAll}  dimV>= {rV}', f'{time.time()-t0:.1f}s')
print('CERTIFIED V = Lambda' if S.A.nvars - rAll == rV else 'NOT EQUAL')
