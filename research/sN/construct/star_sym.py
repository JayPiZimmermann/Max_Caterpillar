"""Is max_N in span(V1 + out-star neurons sigma(sum_o s_o sigma(x_o-x_c)), s in {-1,0,1})?
S_N-symmetric reduction: one chamber x_1>...>x_N, weights depend on type (p,m)=(#+1,#-1).
Exact rational. Coordinates on the chamber: gaps d_1..d_{N-1} (d_i=x_i-x_{i+1}) and x_N."""
import sys, itertools
from math import comb, gcd
from fractions import Fraction as Fr
from linalg import solve
N = int(sys.argv[1]); SMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 1
vals = list(range(-SMAX, SMAX + 1))
types = {}  # (sorted multiset of nonzero s values over all N-1 leaves) -> var
def tvar(t):
    if t not in types: types[t] = len(types)
    return types[t]
# linear piece accumulators: dict var -> vector over (d_1..d_{N-1}, xN)
lin = {}   # (coord) -> {var: coef}
cross = {} # class -> {var: coef}
def add(dct, key, var, c):
    e = dct.setdefault(key, {}); e[var] = e.get(var, 0) + c
from collections import Counter
for c in range(1, N + 1):          # center position
    nb = N - c                     # leaves below
    # completions below: multiset counts of values
    below = Counter()
    for sb in itertools.product(vals, repeat=nb):
        below[tuple(sorted(v for v in sb if v))] += 1
    for sa in itertools.product(vals, repeat=c - 1):
        P = list(itertools.accumulate(sa))
        pos = any(p > 0 for p in P); neg = any(p < 0 for p in P)
        above = [v for v in sa if v]
        for bt, mult in below.items():
            var = tvar(tuple(sorted(above + list(bt))))
            if not pos and not neg: continue  # g == 0 on chamber? only if P all zero -> sigma(0)=0
            if not neg:   # sigma(g)=g, g=sum_{i<c} d_i P_i
                for i, p in enumerate(P):
                    if p: add(lin, i, var, mult * p)
            elif not pos:
                pass
            else:
                g = 0
                for p in P: g = gcd(g, abs(p))
                first = next(p for p in P if p)
                sgn = 1 if first > 0 else -1
                key = tuple(sgn * p // g for p in P) + (0,) * (N - c)  # pad to N-1 gaps... 
                key = key[:N - 1]
                lam = sgn * g  # g_neuron = lam * key.d
                add(cross, key, var, mult * abs(lam))
                if lam < 0:  # linear part w*lam*key.d
                    for i, p in enumerate(key):
                        if p: add(lin, i, var, mult * lam * p)
nv = len(types); A = nv; B = nv + 1  # V1 symmetric: A*sum_{i<j} m_ij + B*sum x_i  (only symmetric parts matter)
# but general V1 allowed: by symmetry, symmetric V1 part suffices.
rows, rhs = [], []
for key, e in cross.items(): rows.append(e); rhs.append(0)
# sum_{i<j} m_ij = sum_i (N-i) x_i ; x_i = xN + sum_{j>=i} d_j  -> coef of d_j: sum_{i<=j}(N-i); xN: sum_i (N-i)
for j in range(N - 1):
    e = dict(lin.get(j, {}))
    e[A] = e.get(A, 0) + sum(N - i for i in range(1, j + 2))
    e[B] = e.get(B, 0) + (j + 1)
    rows.append(e); rhs.append(1)   # target x_1 = xN + sum d
e = {A: comb(N, 2), B: N}; rows.append(e); rhs.append(1)
ok, sol, piv, free = solve(rows, rhs, nv + 2)
print('N', N, 'SMAX', SMAX, 'types', nv, 'cross classes', len(cross), 'consistent', ok)
if ok:
    inv = {v: k for k, v in types.items()}
    print('free', len(free))
    for v, val in sorted(sol.items()):
        if v < nv and val: print(inv[v], val)
        elif v >= nv: print('A' if v == A else 'B', val)
