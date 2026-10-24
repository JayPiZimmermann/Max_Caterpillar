"""Rueß-type atoms sigma(sum_A m_ij - sum_B m_ij), A,B disjoint k-edge forests (sets).
S_n-symmetric identity-chamber test (types via WL hash of 2-coloured graph, orbit-invariant).
python fam_ruess.py n k"""
import sys, itertools, hashlib
import numpy as np
from collections import Counter
from classify import top_test, build
from modp import rank_mod, P as PR
from math import comb
n = int(sys.argv[1]); k = int(sys.argv[2])
E = list(itertools.combinations(range(n), 2))
def forest(es):
    par = list(range(n))
    def f(a):
        while par[a] != a: par[a] = par[par[a]]; a = par[a]
        return a
    for a, b in es:
        ra, rb = f(a), f(b)
        if ra == rb: return False
        par[ra] = rb
    return True
F = [es for es in itertools.combinations(E, k) if forest(es)]
def wl(A, B):
    col = [0] * n
    for it in range(3):
        sig = []
        for v in range(n):
            na = sorted(col[u] for (a, b) in A for u in (a, b) if v in (a, b) and u != v)
            nb = sorted(col[u] for (a, b) in B for u in (a, b) if v in (a, b) and u != v)
            sig.append((col[v], tuple(na), tuple(nb)))
        m = {s: i for i, s in enumerate(sorted(set(sig)))}
        col = [m[s] for s in sig]
    h = tuple(sorted(Counter(sig).items()))
    return h
neur = []
for A in F:
    for B in F:
        if set(A) & set(B): continue
        t = wl(A, B); t2 = wl(B, A)
        t = min(str(t), str(t2))     # swap symmetry handled loosely: sigma(-g) = sigma(g) - g
        a = np.zeros(n, dtype=np.int64)
        for (i, j) in A: a[i] += 1        # identity chamber: min index = higher value
        for (i, j) in B: a[i] -= 1
        if a.any(): neur.append((hashlib.md5(t.encode()).hexdigest(), a, 1))
ok, nc, nv = top_test(n, neur)
print('n', n, 'k', k, 'atoms', len(neur), 'types', nv, 'cross', nc, 'TOP', ok, flush=True)
