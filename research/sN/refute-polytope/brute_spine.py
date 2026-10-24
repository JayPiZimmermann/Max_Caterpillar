#!/usr/bin/env python3
"""Independent brute force of Q_C(r) for abstract caterpillar components
(spine s_0..s_{L-1}, root s_0, a_j hinge leaves at s_j, kappa = childdeg + lambda),
counting orders by DP (no hook formula). Condition (b) only in the weak form
't in S with no F-neighbour in S has kappa_t != 0'. Reports max Q(r)."""
import itertools, sys
from fractions import Fraction as F
from functools import lru_cache

def Q(lam, a, r):
    L = len(lam)
    # vertices: spine 0..L-1, then leaves
    adj = {j: set() for j in range(L)}
    kap = {}
    leaves_of = {j: [] for j in range(L)}
    nid = L
    for j in range(L):
        for _ in range(a[j]):
            adj[nid] = {j}; adj[j].add(nid); leaves_of[j].append(nid); kap[nid] = 0; nid += 1
        if j + 1 < L:
            adj[j].add(j + 1); adj[j + 1].add(j)
    for j in range(L):
        child = a[j] + (1 if j + 1 < L else 0)
        kap[j] = child + lam[j]
    V = list(range(nid))
    D = sum(kap.values()) - (nid - 1)
    tot = F(0)
    for mask in range(1 << nid):
        S = {v for v in V if mask >> v & 1}
        ok = True
        for t in S:
            if not (adj[t] & S) and kap[t] == 0:
                ok = False; break
        if not ok: continue
        O = [v for v in V if v not in S]
        n = len(O); idx = {v: i for i, v in enumerate(O)}
        # DP: place from top; above(o) = placed nbrs + nbrs in S
        cnt = [0] * (1 << n); cnt[0] = 1
        for st in range(1 << n):
            if not cnt[st]: continue
            for i, o in enumerate(O):
                if st >> i & 1: continue
                above = sum(1 for w in adj[o] if w in S or (w in idx and st >> idx[w] & 1))
                if above == kap[o]:
                    cnt[st | 1 << i] += cnt[st]
        if cnt[-1] == 0: continue
        from math import factorial
        tot += F(cnt[-1], factorial(n)) * r ** len(S)
    return r ** D * tot

r = F(1, int(sys.argv[1])) if len(sys.argv) > 1 else F(1, 4)
best = (F(0), None)
for L in range(1, 6):
    amax = 2 if L <= 3 else 1
    for lam in itertools.product([-1, 0, 1, 2], *([[0, 1, 2]] * (L - 1))):
        for a in itertools.product(range(amax + 1), repeat=L):
            if L == 1 and a[0] == 0: continue
            q = Q(lam, a, r)
            if q > best[0]:
                best = (q, (lam, a))
    print('L<=', L, 'max Q =', best[0], float(best[0]), best[1], flush=True)
