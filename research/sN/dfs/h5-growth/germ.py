"""Generalized ('germ') units for the local recursion s_N >= C(N,m) s'_m / max_u W_m(u).
At an m-locality the germ of a passing unit is sigma(<v,z> + sum_{(i,j) in F} sigma(z_i - z_j))
with v in Z^m, sum v = 0, F = pairs of M inside T (an induced subforest of a caterpillar).
Here: all v with |v_i| <= B, sum v = 0, and all forests F on [m] (normalized i<j),
excluding auxiliary functions (F empty, v a multiple of e_i - e_j, or v = 0).
Builds the kink/Moebius system of kf.py for this unit list.
usage: python germ.py m B out.pkl
"""
import itertools
import pickle
import sys

import numpy as np

from kf import unit_kinks, mobius_row, subsets3

m, B, OUT = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
pairs = list(itertools.combinations(range(m), 2))


def is_forest(F):
    par = list(range(m))

    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for i, j in F:
        a, b = f(i), f(j)
        if a == b:
            return False
        par[a] = b
    return True


forests = [frozenset(F) for r in range(m) for F in itertools.combinations(pairs, r) if is_forest(F)]
heads = [v for v in itertools.product(range(-B, B + 1), repeat=m) if sum(v) == 0]


def aux(v, F):
    if F:
        return False
    nz = [x for x in v if x]
    return len(nz) == 0 or (len(nz) == 2 and nz[0] == -nz[1])


U0 = {(v, F) for F in forests for v in heads if not aux(v, F)}
perms = list(itertools.permutations(range(m)))


def norm(h, prs):
    h = list(h); M = []
    for a, b in prs:
        if a > b:
            h[a] += 1; h[b] -= 1; a, b = b, a
        M.append((a, b))
    return (tuple(h), frozenset(M))


def pk(key, p):
    h, M = key
    h2 = [0] * m
    for i in range(m):
        h2[p[i]] = h[i]
    return norm(h2, [(p[a], p[b]) for a, b in M])


U = sorted({pk(k, p) for k in U0 for p in perms})   # closed under S_m
groups = {}
for u, key in enumerate(U):
    for p, d, lam in unit_kinks(m, key, perms):
        groups.setdefault((p, d), {})[u] = lam
Dm = np.array([mobius_row(k, m) for k in U], dtype=np.int64).T
tD = np.array([(-1) ** (len(S) + 1) for S in subsets3(m)], dtype=np.int64)
# drop units with zero column (no kinks, all D_S = 0): they lie in the local auxiliary span
used = {u for g in groups.values() for u in g} | set(np.nonzero(np.abs(Dm).sum(0))[0].tolist())
keep = sorted(used)
remap = {u: i for i, u in enumerate(keep)}
U2 = [U[u] for u in keep]
groups2 = {k: {remap[u]: l for u, l in g.items()} for k, g in groups.items()}
pickle.dump((U2, groups2, Dm[:, keep], tD), open(OUT, 'wb'))
print('m', m, 'B', B, 'forests', len(forests), 'units', len(U), 'nonzero columns', len(U2), 'groups', len(groups2))
