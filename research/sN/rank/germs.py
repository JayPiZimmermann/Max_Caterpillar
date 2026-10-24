#!/usr/bin/env python3
"""Local germs of caterpillar units at m-tie localities (research/sN/rank/germs.py).

Locality L = (T, rho), |T| = m, p_t = 0 on T, outside coordinates at -B^{rho(o)}.
For z supported on T, A_k(p_L + z) = A_k(p_L) + G_k(z) with
    G_k(z) = <v, z> + sum_{(p,c) inner hinges} relu(z_p - z_c)
(v, inner) as in global/mixed_m.py.  When A_k(p_L) = 0 the germ of U_k is relu(G_k);
when A_k(p_L) != 0 the germ is linear + hinges in T (auxiliary).

Germ class G_m(N): all relu(G_k) (normalized as m-variable keys, T relabelled in
increasing label order) over units k and localities with A_k(p_L) = 0, closed under
S_m (relabelling within T; the dictionary is closed under relabelling).

This module enumerates, for each unit (identity labelling, apex 0, as in
global/mixed_fast.py), the T with at least one valid order, the number of valid
orders, and the germ.
"""
import itertools
import math
from fractions import Fraction


def relu(t):
    return t if t > 0 else 0


def caterpillar(N, S):
    r = N - 2
    edges = []
    for j in range(1, r + 1):
        p = max([0] + [i for i in S if i < j])
        edges.append((p + 1, j + 1))
    return edges, max(S) + 1


def units(N):
    r = N - 2
    for size in range(1, r + 1):
        for S in itertools.combinations(range(1, r + 1), size):
            edges, last = caterpillar(N, S)
            for states in itertools.product(range(3), repeat=r):
                yield S, states, edges, last


def unit_data(N, edges, last, states):
    kappa = [0] * N
    kappa[0] -= 1
    kappa[last] += 1
    nbr = [[] for _ in range(N)]
    lin, hin = [], []
    for (p, c), s in zip(edges, states):
        if s == 1:
            lin.append((p, c)); kappa[p] += 1; kappa[c] -= 1
        elif s == 2:
            hin.append((p, c)); kappa[p] += 1
            nbr[p].append(c); nbr[c].append(p)
    return kappa, nbr, lin, hin


def count_orders(N, T, kappa, nbr):
    Ts = set(T)
    rest = [o for o in range(N) if o not in Ts]
    idx = {o: k for k, o in enumerate(rest)}
    count = {0: 1}
    for _ in range(len(rest)):
        new = {}
        for placed, c in count.items():
            for o in rest:
                b = 1 << idx[o]
                if placed & b:
                    continue
                above = sum(1 for u in nbr[o] if u in Ts or placed & (1 << idx[u]))
                if above == kappa[o]:
                    new[placed | b] = new.get(placed | b, 0) + c
        count = new
    return sum(count.values())


def germ(T, last, lin, hin):
    """Normalized m-variable key (h, M) of G_k on T (T sorted)."""
    pos = {t: i for i, t in enumerate(T)}
    m = len(T)
    v = [0] * m
    def add(a, b):
        if a in pos: v[pos[a]] += 1
        if b in pos: v[pos[b]] -= 1
    add(last, 0)
    for p, c in lin:
        add(p, c)
    M = []
    for p, c in hin:
        if p in pos and c in pos:
            a, b = pos[p], pos[c]
            if a > b:            # relu(z_a - z_b) = relu(z_b - z_a) + z_a - z_b
                v[a] += 1; v[b] -= 1
                a, b = b, a
            M.append((a, b))
        elif p in pos:
            v[pos[p]] += 1       # p above c: hinge active, linear
    return (tuple(v), frozenset(M))


def relabel(key, perm):
    """Apply a permutation of the m variables to a normalized key."""
    h, M = key
    m = len(h)
    v = [0] * m
    for i in range(m):
        v[perm[i]] += h[i]
    MM = []
    for a, b in M:
        a, b = perm[a], perm[b]
        if a > b:
            v[a] += 1; v[b] -= 1
            a, b = b, a
        MM.append((a, b))
    return (tuple(v), frozenset(MM))


def localities(N, m, need_pass=True):
    """Yield (unit_id, T, count, germ) for every unit and m-set T with count > 0
    valid orders (A_k(p_L) = 0)."""
    uid = 0
    for S, states, edges, last in units(N):
        kappa, nbr, lin, hin = unit_data(N, edges, last, states)
        forced = [o for o in range(N) if kappa[o] < 0 or kappa[o] > len(nbr[o])]
        if len(forced) <= m:
            cand = [o for o in range(N) if o not in forced]
            for extra in itertools.combinations(cand, m - len(forced)):
                T = tuple(sorted(forced + list(extra)))
                Ts = set(T)
                ok = True
                for o in range(N):
                    if o in Ts:
                        continue
                    inT = sum(1 for u in nbr[o] if u in Ts)
                    if kappa[o] - inT < 0 or kappa[o] - inT > len(nbr[o]) - inT:
                        ok = False
                        break
                if not ok:
                    continue
                c = count_orders(N, T, kappa, nbr)
                if c:
                    yield uid, (S, states), T, c, germ(T, last, lin, hin)
        uid += 1
