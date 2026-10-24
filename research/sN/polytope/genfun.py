#!/usr/bin/env python3
"""Per-component generating functions for the m-locality mixed-difference test
(research/sN/polytope/genfun.py).

Unit in tree form (as global/mixed_fast.py): caterpillar on labels 0..N-1, apex 0,
root 1, edge states 0 omit / 1 lin / 2 hinge.  kappa as in NOTE.md.
For a locality (T, rho), necessary pass conditions (NOTE.md + global/mixed_fast.py):
  (a) every o outside T has exactly kappa_o hinge neighbours above it
      (T above everything, rho orders the outside);
  (b) every t in T has kappa_t != 0 or a hinge neighbour in T.
Both conditions are local to components of the hinge forest F, and the relative
orders of a uniform random permutation on disjoint sets are independent, so
  G_k(x) := sum_T Pr_rho[(a)] [(b)] x^|T| = prod_C P_C(x),
  P_C(x) = sum_{S subset C} p_C(S) [(b) on S] x^|S|.
W_m(k) = [x^m] G_k  >= the mixed_fast weight.  Exact Fractions throughout.
Usage: python3 genfun.py N
"""
import itertools
import math
import sys
from fractions import Fraction
from functools import lru_cache


def caterpillar(N, S):
    r = N - 2
    edges = []
    for j in range(1, r + 1):
        p = max([0] + [i for i in S if i < j])
        edges.append((p + 1, j + 1))
    return edges, max(S) + 1


def unit_data(N, edges, last, states):
    kappa = [0] * N
    kappa[0] -= 1
    kappa[last] += 1
    hin = []
    for (p, c), s in zip(edges, states):
        if s == 1:
            kappa[p] += 1; kappa[c] -= 1
        elif s == 2:
            kappa[p] += 1; hin.append((p, c))
    return kappa, hin


def components(N, hin):
    nbr = [[] for _ in range(N)]
    for p, c in hin:
        nbr[p].append(c); nbr[c].append(p)
    seen, comps = [False] * N, []
    for v in range(N):
        if seen[v]:
            continue
        st, comp = [v], []
        seen[v] = True
        while st:
            u = st.pop(); comp.append(u)
            for w in nbr[u]:
                if not seen[w]:
                    seen[w] = True; st.append(w)
        comps.append(sorted(comp))
    return comps, nbr


def canon(comp, nbr, kappa):
    """Hashable description of a component: (n, kappa tuple, edge set) relabelled 0..n-1."""
    idx = {v: i for i, v in enumerate(comp)}
    E = tuple(sorted((idx[u], idx[w]) for u in comp for w in nbr[u] if idx[u] < idx[w]))
    return (len(comp), tuple(kappa[v] for v in comp), E)


@lru_cache(maxsize=None)
def comp_poly(key):
    """Coefficient list of P_C(x) (Fractions)."""
    n, kap, E = key
    nb = [[] for _ in range(n)]
    for u, w in E:
        nb[u].append(w); nb[w].append(u)
    coef = [Fraction(0)] * (n + 1)
    for mask in range(1 << n):
        S = [i for i in range(n) if mask >> i & 1]
        # (b)
        if any(kap[t] == 0 and not any(mask >> u & 1 for u in nb[t]) for t in S):
            continue
        rest = [i for i in range(n) if not mask >> i & 1]
        if not rest:
            coef[n] += 1
            continue
        ridx = {o: k for k, o in enumerate(rest)}
        # quick prune
        bad = False
        for o in rest:
            inS = sum(1 for u in nb[o] if mask >> u & 1)
            if kap[o] < inS or kap[o] > len(nb[o]):
                bad = True; break
        if bad:
            continue
        cnt = {0: 1}
        for _ in rest:
            new = {}
            for placed, c in cnt.items():
                for o in rest:
                    b = 1 << ridx[o]
                    if placed & b:
                        continue
                    above = sum(1 for u in nb[o] if (mask >> u & 1) or (u in ridx and placed >> ridx[u] & 1))
                    if above == kap[o]:
                        new[placed | b] = new.get(placed | b, 0) + c
            cnt = new
        tot = sum(cnt.values())
        if tot:
            coef[len(S)] += Fraction(tot, math.factorial(len(rest)))
    return tuple(coef)


def polymul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def unit_poly(N, edges, last, states):
    kappa, hin = unit_data(N, edges, last, states)
    comps, nbr = components(N, hin)
    g = [Fraction(1)]
    keys = []
    for comp in comps:
        k = canon(comp, nbr, kappa)
        keys.append(k)
        g = polymul(g, comp_poly(k))
    return g, keys


def all_units(N):
    r = N - 2
    for size in range(1, r + 1):
        for S in itertools.combinations(range(1, r + 1), size):
            edges, last = caterpillar(N, S)
            for states in itertools.product(range(3), repeat=r):
                yield S, states, edges, last


if __name__ == '__main__':
    N = int(sys.argv[1])
    rs = [Fraction(1, d) for d in (1, 2, 3, 4, 6, 8)]
    Wm = [Fraction(0)] * (N + 1)
    Gmax = {r: (Fraction(0), None) for r in rs}
    for S, states, edges, last in all_units(N):
        g, keys = unit_poly(N, edges, last, states)
        for m in range(len(g)):
            if g[m] > Wm[m]:
                Wm[m] = g[m]
        for r in rs:
            val = sum(c * r ** i for i, c in enumerate(g))
            if val > Gmax[r][0]:
                Gmax[r] = (val, (S, states))
    print(f'N={N}: W_m(a,b) for m=0..N:', [str(w) for w in Wm])
    for r in rs:
        print(f'  max_k G_k({r}) = {Gmax[r][0]} ({float(Gmax[r][0]):.4f}) at {Gmax[r][1]}')
    comps = list(comp_poly.cache_info())
    print('  distinct components:', comps)
