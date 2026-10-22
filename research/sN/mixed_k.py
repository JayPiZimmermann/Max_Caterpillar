#!/usr/bin/env python3
"""Mixed-difference localities over a k-set T (main-session branch).

Locality L = (T, order), |T| = k >= 3: coordinates in T tie at 0, the others lie
below in the given order. Functional: the k-th mixed finite difference in the
T-coordinates at p_L. It kills affine functions and every function that does
not depend on some coordinate of T near p_L (in particular all auxiliary
functions, which depend on <= 2 coordinates), and is nonzero on max_N.

A unit can be nonzero only if
  (a) its outer argument vanishes at p_L: every outside o has exactly kappa_o
      hinge-neighbours above it (as for k = 3), and
  (s) its germ depends on every t in T: each t in T has v_t != 0 or is an
      endpoint of a hinge inside T, where v_t is the T-part of the outer slope.
This script reports, per N and k, the maximum over units of the number of
localities passing (a) and (s), and the resulting covering bound
  s_N >= C(N,k) (N-k)! / max.

Usage: python3 research/sN/mixed_k.py N k
"""
import itertools, math, sys
N = int(sys.argv[1]); k = int(sys.argv[2])
r = N - 2


def caterpillar(S):
    edges = []
    for j in range(1, r + 1):
        p = max([0] + [i for i in S if i < j])
        edges.append((p + 1, j + 1))
    return edges, max(S) + 1


best = 0; best_cfg = None
for size in range(1, r + 1):
    for S in itertools.combinations(range(1, r + 1), size):
        edges, last = caterpillar(S)
        for states in itertools.product(range(3), repeat=r):
            mu = [0] * N; nbr = [[] for _ in range(N)]
            mu[0] += 1; mu[last] -= 1
            for (p, c), s in zip(edges, states):
                if s: mu[c] += 1
                if s == 1: mu[p] -= 1
                if s == 2: nbr[p].append(c); nbr[c].append(p)
            total = 0
            for T in itertools.combinations(range(N), k):
                Ts = set(T)
                rest = [o for o in range(N) if o not in Ts]
                if any(mu[o] < 0 or mu[o] > len(nbr[o]) for o in rest): continue
                # (s): support of the germ covers T
                v = {t: 0 for t in T}
                v[0 if 0 in Ts else None] = v.get(0, 0) if 0 in Ts else 0
                v = {t: 0 for t in T}
                if 0 in Ts: v[0] -= 1
                if last in Ts: v[last] += 1
                touched = set()
                for (p, c), s in zip(edges, states):
                    if s == 1:
                        if p in Ts: v[p] += 1
                        if c in Ts: v[c] -= 1
                    if s == 2:
                        if p in Ts and c in Ts: touched |= {p, c}
                        elif p in Ts: v[p] += 1          # active: p above c
                if any(v[t] == 0 and t not in touched for t in T): continue
                idx = {o: i for i, o in enumerate(rest)}
                count = {0: 1}
                for _ in range(len(rest)):
                    new = {}
                    for placed, cnt in count.items():
                        for o in rest:
                            b = 1 << idx[o]
                            if placed & b: continue
                            below = sum(1 for u in nbr[o] if u not in Ts and not placed & (1 << idx[u]))
                            if below == mu[o]: new[placed | b] = new.get(placed | b, 0) + cnt
                    count = new
                total += sum(count.values())
            if total > best: best, best_cfg = total, (S, states)
locs = math.comb(N, k) * math.factorial(N - k)
print(f'N={N} k={k}: localities {locs}, max per unit {best} = {best / math.factorial(N - k):.3f} (N-k)!,'
      f' bound s_N >= {locs / best:.3f}; best {best_cfg}', flush=True)
