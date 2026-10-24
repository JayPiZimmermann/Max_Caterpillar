#!/usr/bin/env python3
"""Independent check (no tree model, no Pass criterion): for every dictionary key
(h, M) from scripts/vocabulary_search.dictionary(N), evaluate the six-point test
functional Lambda_L U_k exactly (Fractions) at every locality L and count the
localities with Lambda != 0.  Reports max over keys / (N-3)! (cubic claim: <= 2),
and checks Lambda_L max_N = 2 delta and Lambda kills the auxiliary span.
Usage: python3 research/sN/verify-logic/lambda_direct.py N   (run from repo root)"""
import itertools, math, sys
from fractions import Fraction as Fr
sys.path.insert(0, 'scripts')
from vocabulary_search import dictionary
N = int(sys.argv[1])
K0, _ = dictionary(N)
K0 = list(K0)
relu = lambda t: t if t > 0 else 0
B = 4 * N + 10 + 2 * max(max(abs(x) for x in h) for h, M in K0)
C = 1 + max(sum(abs(x) for x in h) for h, M in K0) + 2 * N
eps = Fr(1, 8 * C); dl = eps / 2
def U(key, y):
    h, M = key
    return relu(sum(hh * yy for hh, yy in zip(h, y)) + sum(relu(y[i] - y[j]) for i, j in M))
def Lam(g, p, a, b):
    def at(q):
        qp = list(q); qm = list(q)
        qp[a] += dl; qp[b] -= dl; qm[a] -= dl; qm[b] += dl
        return g(qp) + g(qm) - 2 * g(q)
    qP = list(p); qP[a] += eps; qP[b] += eps
    qM = list(p); qM[a] -= eps; qM[b] -= eps
    return at(qP) - at(qM)
locs = []
for T in itertools.combinations(range(N), 3):
    rest = [o for o in range(N) if o not in T]
    for perm in itertools.permutations(range(1, N - 2)):
        p = [Fr(0)] * N
        for o, e in zip(rest, perm): p[o] = Fr(-B ** e)
        locs.append((T, p))
# sanity: max and auxiliary functions
for T, p in locs:
    a, b, c = T
    assert Lam(lambda y: max(y), p, a, b) == 2 * dl
    for i in range(N):
        assert Lam(lambda y: relu(y[i]), p, a, b) == 0 and Lam(lambda y: relu(-y[i]), p, a, b) == 0
        for j in range(N):
            if i != j: assert Lam(lambda y: relu(y[i] - y[j]), p, a, b) == 0
best = 0; hist = {}
for key in K0:
    cnt = sum(1 for T, p in locs if Lam(lambda y: U(key, y), p, T[0], T[1]) != 0)
    hist[cnt] = hist.get(cnt, 0) + 1
    best = max(best, cnt)
f = math.factorial(N - 3)
print(f'N={N}: keys={len(K0)} localities={len(locs)} max #(Lambda!=0) per key={best} = {Fr(best, f)} (N-3)!')
print('hist', dict(sorted(hist.items())))
