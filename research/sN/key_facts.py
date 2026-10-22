#!/usr/bin/env python3
"""Check key facts K1-K4 on all normalized descriptions and the triple count.

kappa_o = h_o + |N^+(o)| (N^+(o): hinge neighbours with larger index).
K1 sum h = 0; K2 some a with h_a = -1 and no hinge at a; K3 kappa >= -1;
K4 |M| <= N-2. Also the number of triples T passing (a) [with some order] and
(b'), which should be <= N-2, and the maximal number of such T.
"""
import itertools, sys
sys.path.insert(0, 'scripts')
from vocabulary_search import dictionary, is_auxiliary
N = int(sys.argv[1])
K0, _ = dictionary(N)
fails = {'K1': 0, 'K2': 0, 'K3': 0, 'K4': 0}
maxT = 0
for h, M in K0:
    kap = [h[o] + sum(1 for i, j in M if i == o) for o in range(N)]
    touched = {i for e in M for i in e}
    if sum(h): fails['K1'] += 1
    if not any(h[a] == -1 and a not in touched for a in range(N)): fails['K2'] += 1
    if min(kap) < -1: fails['K3'] += 1
    if len(M) > N - 2: fails['K4'] += 1
    # triples allowed by the counting argument: Neg subset T and kappa sum = |M(T)|, (b')
    neg = {o for o in range(N) if kap[o] < 0}
    cnt = 0
    for T in itertools.combinations(range(N), 3):
        if not neg <= set(T): continue
        mT = sum(1 for i, j in M if i in T and j in T)
        if sum(kap[t] for t in T) != mT: continue
        v = {t: kap[t] - sum(1 for i, j in M if i == t and j in T) for t in T}
        root_like = sorted(x for x in v.values() if x) in ([], ) or (
            len([x for x in v.values() if x]) == 2 and sum(v.values()) == 0)
        if mT == 0 and root_like: continue
        cnt += 1
    maxT = max(maxT, cnt)
print(N, 'units', len(K0), 'fails', fails, 'max admissible triples', maxT, 'N-2 =', N - 2)
