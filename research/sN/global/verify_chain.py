#!/usr/bin/env python3
"""Exhaustive check of every step of the component bound for W_m(N)
(global/verify_chain.py).  For each caterpillar unit and each m:

  q_C(X) := P[ random order of C\\X, X above all, gives every o in C\\X
               exactly kappa_o hinge neighbours above it ]
  G_C(x) := sum over X subset C, X locally active, of q_C(X) x^{|X|}
  (locally active: each t in X has kappa_t != 0 or a hinge neighbour in X)

Checked claims (all exact, Fractions):
  (E)  p_T = prod_C q_C(T cap C) for every T passing the mixed test;
  (L1) q_C(empty) <= 1/2 for every component with >= 2 vertices;
  (L2) if X is locally active with q_C(X) > 0, then a non-spine vertex of C
       lies in X iff its spine parent does;
  (L3) q_C(X) <= prod over maximal runs R of outside spine vertices of
       2^{-floor(|R|/2)};
  (P)  W_m(unit) <= [x^m] prod_C G_C(x).
Usage: python3 verify_chain.py N
"""
import itertools
import math
import sys
from fractions import Fraction

N = int(sys.argv[1])
sys.argv = ['x', str(N), '3']
import mixed_fast as mf

r = N - 2


def q_of(C, X, kappa, nbr):
    Xs = set(X)
    rest = [o for o in C if o not in Xs]
    if not rest:
        return Fraction(1)
    idx = {o: k for k, o in enumerate(rest)}
    count = {0: 1}
    for _ in range(len(rest)):
        new = {}
        for placed, c in count.items():
            for o in rest:
                b = 1 << idx[o]
                if placed & b:
                    continue
                above = sum(1 for u in nbr[o] if u in Xs or placed & (1 << idx[u]))
                if above == kappa[o]:
                    new[placed | b] = new.get(placed | b, 0) + c
        count = new
    return Fraction(sum(count.values()), math.factorial(len(rest)))


def polymul(a, b, cap):
    out = [Fraction(0)] * (cap + 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if i + j > cap:
                break
            out[i + j] += x * y
    return out


fails = {'E': 0, 'L1': 0, 'L2': 0, 'L3': 0, 'P': 0}
nunits = 0
ratio_max = {}
for size in range(1, r + 1):
    for S in itertools.combinations(range(1, r + 1), size):
        edges, last = mf.caterpillar(S)
        spine = sorted({1} | {s + 1 for s in S})
        parent = {c: p for p, c in edges}
        for states in itertools.product(range(3), repeat=r):
            nunits += 1
            kappa = [0] * N
            kappa[0] -= 1
            kappa[last] += 1
            nbr = [[] for _ in range(N)]
            for (p, c), s in zip(edges, states):
                if s == 1:
                    kappa[p] += 1; kappa[c] -= 1
                elif s == 2:
                    kappa[p] += 1; nbr[p].append(c); nbr[c].append(p)
            # components
            seen, comps = set(), []
            for v in range(N):
                if v in seen:
                    continue
                stack, comp = [v], []
                seen.add(v)
                while stack:
                    u = stack.pop(); comp.append(u)
                    for w in nbr[u]:
                        if w not in seen:
                            seen.add(w); stack.append(w)
                comps.append(sorted(comp))
            compof = {v: i for i, C in enumerate(comps) for v in C}
            G, Q = [], []
            for C in comps:
                g = [Fraction(0)] * (len(C) + 1)
                qd = {}
                for k in range(len(C) + 1):
                    for X in itertools.combinations(C, k):
                        Xs = set(X)
                        if any(kappa[t] == 0 and not any(u in Xs for u in nbr[t]) for t in X):
                            continue
                        q = q_of(C, X, kappa, nbr)
                        qd[X] = q
                        g[k] += q
                        if q == 0:
                            continue
                        # L2
                        for v in C:
                            if v not in spine and len(C) > 1:
                                if (v in Xs) != (parent[v] in Xs):
                                    fails['L2'] += 1
                        # L3
                        sp = [v for v in spine if v in C]
                        bound = Fraction(1)
                        run = 0
                        for v in sp + [None]:
                            if v is not None and v not in Xs:
                                run += 1
                            else:
                                bound /= 2 ** (run // 2)
                                run = 0
                        if q > bound:
                            fails['L3'] += 1
                if len(C) >= 2 and qd.get((), 0) > Fraction(1, 2):
                    fails['L1'] += 1
                G.append(g)
                Q.append(qd)
            prod = [Fraction(1)]
            for g in G:
                prod = polymul(prod, g, N)
            for m in range(3, N + 1):
                sys_m = m
                mf.m = m
                W, info = mf.unit_weight(edges, last, states)
                bound = prod[m] if m < len(prod) else Fraction(0)
                if W > bound:
                    fails['P'] += 1
                if W:
                    ratio_max[m] = max(ratio_max.get(m, 0), W / bound)
                if info:
                    for T, w in info[3]:
                        pt = Fraction(1)
                        for i, C in enumerate(comps):
                            X = tuple(v for v in C if v in T)
                            pt *= Q[i].get(X, Fraction(0))
                        if pt != w:
                            fails['E'] += 1
print(f'N={N}: units {nunits}; failures {fails}; max W/[x^m]prod by m:',
      {m: float(v) for m, v in sorted(ratio_max.items())})
