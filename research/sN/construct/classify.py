"""Build symmetric top system from neurons (type, a-vector, mult); test via mod-p ranks.
Returns (top_achievable, ncross, ntypes, data)."""
import numpy as np
from math import comb, gcd
from modp import rank_mod, P
def build(N, neurons):
    types = {}; lin = {}; cross = {}
    def add(d, key, var, c):
        e = d.setdefault(key, {}); e[var] = e.get(var, 0) + c
    for t, a, mult in neurons:
        var = types.setdefault(t, len(types))
        D = np.cumsum(a)[:-1]
        if D.max() > 0 and D.min() >= 0:
            for i in np.nonzero(D)[0]: add(lin, int(i), var, mult * int(D[i]))
        elif D.max() > 0 and D.min() < 0:
            g = int(np.gcd.reduce(np.abs(D)))
            first = int(D[np.nonzero(D)[0][0]]); sgn = 1 if first > 0 else -1
            key = tuple(int(x) for x in (sgn * D) // g); lam = sgn * g
            add(cross, key, var, mult * abs(lam))
            if lam < 0:
                for i, d in enumerate(key):
                    if d: add(lin, i, var, mult * lam * d)
    nv = len(types)
    ellD = {}
    for r in range(1, N + 1):
        w = (-1) ** (r - 1) * comb(N - 1, r - 1)
        if r - 1 < N - 1: ellD[r - 1] = ellD.get(r - 1, 0) + w
        if r - 2 >= 0: ellD[r - 2] = ellD.get(r - 2, 0) - w
    ell = {}
    for i, w in ellD.items():
        for var, cc in lin.get(i, {}).items(): ell[var] = ell.get(var, 0) + w * cc
    return types, lin, cross, ell
def top_test(N, neurons):
    types, lin, cross, ell = build(N, neurons)
    nv = len(types)
    C = np.zeros((len(cross), nv), dtype=np.int64)
    for i, e in enumerate(cross.values()):
        for v, c in e.items(): C[i, v] = c % P
    L = np.zeros((1, nv), dtype=np.int64)
    for v, c in ell.items(): L[0, v] = c % P
    if not L.any(): return False, len(cross), nv
    r1 = rank_mod(C) if len(cross) else 0
    r2 = rank_mod(np.vstack([C, L]))
    return r2 > r1, len(cross), nv
