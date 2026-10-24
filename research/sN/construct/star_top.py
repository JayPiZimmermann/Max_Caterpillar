"""Symmetric out-star combos on n variables: crossing cancellation in the identity chamber
(=> braid-PL L-statistic f), then top functional ell(f)=sum_r (-1)^(r-1) C(n-1,r-1) f_r.
If some solution has ell != 0, then max_n = (1/ell)(F - lower max_T combos)."""
import sys, itertools
from math import comb, gcd
from fractions import Fraction as Fr
from collections import Counter
from linalg import solve
N = int(sys.argv[1]); SMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 1
vals = list(range(-SMAX, SMAX + 1))
types = {}
def tvar(t):
    if t not in types: types[t] = len(types)
    return types[t]
lin = {}; cross = {}
def add(dct, key, var, c):
    e = dct.setdefault(key, {}); e[var] = e.get(var, 0) + c
for c in range(1, N + 1):
    nb = N - c
    below = Counter()
    for sb in itertools.product(vals, repeat=nb):
        below[tuple(sorted(v for v in sb if v))] += 1
    for sa in itertools.product(vals, repeat=c - 1):
        P = list(itertools.accumulate(sa))
        pos = any(p > 0 for p in P); neg = any(p < 0 for p in P)
        above = [v for v in sa if v]
        for bt, mult in below.items():
            var = tvar(tuple(sorted(above + list(bt))))
            if not neg and pos:
                for i, p in enumerate(P):
                    if p: add(lin, i, var, mult * p)
            elif pos and neg:
                g = 0
                for p in P: g = gcd(g, abs(p))
                first = next(p for p in P if p); sgn = 1 if first > 0 else -1
                key = tuple(sgn * p // g for p in P) + (0,) * (N - c)
                lam = sgn * g
                add(cross, key, var, mult * abs(lam))
                if lam < 0:
                    for i, p in enumerate(key):
                        if p: add(lin, i, var, mult * lam * p)
nv = len(types)
# f in gap coords: F = sum_i D_i d_i (translation-invariant); L-statistic coefficients f_r = D_r - D_{r-1} (D_0=0, D_N=0)
# ell(f) = sum_r (-1)^(r-1) C(N-1,r-1) f_r  -> linear functional of D:
ellD = {}
for r in range(1, N + 1):
    w = (-1) ** (r - 1) * comb(N - 1, r - 1)
    if r - 1 < N - 1: ellD[r - 1] = ellD.get(r - 1, 0) + w      # +D_r  (index r-1)
    if r - 2 >= 0: ellD[r - 2] = ellD.get(r - 2, 0) - w          # -D_{r-1}
ellrow = {}
for i, w in ellD.items():
    for var, cc in lin.get(i, {}).items(): ellrow[var] = ellrow.get(var, 0) + w * cc
rows = list(cross.values()); rhs = [0] * len(rows)
rows.append(ellrow); rhs.append(1)
ok, sol, piv, free = solve(rows, rhs, nv)
print('N', N, 'SMAX', SMAX, 'types', nv, 'cross classes', len(cross), 'top achievable', ok)
if ok:
    inv = {v: k for k, v in types.items()}
    for v, val in sorted(sol.items()):
        if val: print(' ', inv[v], val)
