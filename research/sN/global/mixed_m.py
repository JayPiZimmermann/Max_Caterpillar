#!/usr/bin/env python3
"""m-tie localities tested with the MIXED m-th difference (global/mixed_m.py).

Locality L = (T, rho): |T| = m, x_T = 0, the N-m other coordinates at
-B^{rho(o)} (distinct scales).  Test functional
    D_L f = sum_{S subset T} (-1)^{m-|S|} f(p_L + delta * 1_S).
D_L kills every function that, on the cube, does not depend on some variable
of T; in particular all auxiliary functions (they depend on <= 2 variables,
m >= 3), linear functions, and every unit with A_k(p_L) != 0 (then U_k is 0
or A_k = linear + 2-variable hinges on the cube).  D_L max_N = (-1)^{m+1} delta.
Hence, for every expansion, each locality is "passed" by some unit of K, and
    s_N >= C(N,m) / W_m(N),   W_m(N) := max_k sum_T p_T(k),
p_T(k) = (#orders rho with A_k(p_L)=0 and D_L U_k != 0) / (N-m)!.

The script enumerates the caterpillar units with identity labelling (the count
is invariant under relabelling; apex = 0) in tree form (edge states
omit/lin/hinge), and computes W_m(N) exactly (Fractions).

Usage: python3 mixed_m.py N m [--check]
"""
import itertools
import math
import sys
from fractions import Fraction

N = int(sys.argv[1])
m = int(sys.argv[2])
CHECK = '--check' in sys.argv
r = N - 2


def relu(t):
    return t if t > 0 else 0


def caterpillar(S):
    edges = []
    for j in range(1, r + 1):
        p = max([0] + [i for i in S if i < j])
        edges.append((p + 1, j + 1))          # (parent, child) labels 1..N-1
    return edges, max(S) + 1                  # last spine vertex


def unit_data(edges, last, states):
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


def restricted(T, last, lin, hin):
    """v_T and inner hinges of A(p_L + z) - A(p_L) for z supported on T."""
    Ts = set(T)
    v = {t: 0 for t in T}
    def add(a, b):
        if a in Ts: v[a] += 1
        if b in Ts: v[b] -= 1
    add(last, 0)
    for p, c in lin:
        add(p, c)
    inner = []
    for p, c in hin:
        if p in Ts and c in Ts:
            inner.append((p, c))
        elif p in Ts:
            v[p] += 1                        # active: p above c
    return v, inner


def mixed(T, v, inner):
    tot = 0
    for size in range(len(T) + 1):
        for S in itertools.combinations(T, size):
            Ss = set(S)
            a = sum(v[t] for t in S) + sum(relu((p in Ss) - (c in Ss)) for p, c in inner)
            tot += (-1) ** (len(T) - size) * relu(a)
    return tot


def count_orders(T, kappa, nbr):
    rest = [o for o in range(N) if o not in T]
    Ts = set(T)
    for o in rest:
        if kappa[o] < 0 or kappa[o] > len(nbr[o]):
            return 0
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


def direct_check(T, order, last, lin, hin, expect):
    """Evaluate the full unit at the locality cube with exact integers."""
    B = 10 ** 3
    big = 10 ** 6        # delta = 1/big, scale everything by big
    pos = [0] * N
    for k, o in enumerate(order):
        pos[o] = -B ** (k + 1) * big
    tot = 0
    for size in range(m + 1):
        for S in itertools.combinations(T, size):
            y = list(pos)
            for t in S:
                y[t] += 1
            A = y[last] - y[0] + sum(y[p] - y[c] for p, c in lin) + sum(relu(y[p] - y[c]) for p, c in hin)
            tot += (-1) ** (m - size) * relu(A)
    return tot == expect


best = Fraction(0)
best_cfg = None
hist = {}
nonzero_units = 0
for size in range(1, r + 1):
    for S in itertools.combinations(range(1, r + 1), size):
        edges, last = caterpillar(S)
        for states in itertools.product(range(3), repeat=r):
            kappa, nbr, lin, hin = unit_data(edges, last, states)
            neg = [o for o in range(N) if kappa[o] < 0]
            if len(neg) > m:
                continue
            W = Fraction(0)
            for T in itertools.combinations(range(N), m):
                if any(o not in T for o in neg):
                    continue
                v, inner = restricted(T, last, lin, hin)
                d = mixed(T, v, inner)
                if d == 0:
                    continue
                c = count_orders(T, kappa, nbr)
                if c == 0:
                    continue
                if CHECK:
                    rest = [o for o in range(N) if o not in T]
                    for order in itertools.permutations(rest):
                        pass
                W += Fraction(c, math.factorial(N - m))
            if CHECK:
                # brute force over all localities for this unit
                Wb = Fraction(0)
                for T in itertools.combinations(range(N), m):
                    rest = [o for o in range(N) if o not in T]
                    v, inner = restricted(T, last, lin, hin)
                    for order in itertools.permutations(rest):
                        B = 10 ** 3; big = 10 ** 6
                        pos = [0] * N
                        for k, o in enumerate(order):
                            pos[o] = -B ** (k + 1) * big
                        tot = 0
                        for sz in range(m + 1):
                            for SS in itertools.combinations(T, sz):
                                y = list(pos)
                                for t in SS:
                                    y[t] += 1
                                A = y[last] - y[0] + sum(y[p] - y[c] for p, c in lin) + \
                                    sum(relu(y[p] - y[c]) for p, c in hin)
                                tot += (-1) ** (m - sz) * relu(A)
                        if tot != 0:
                            Wb += Fraction(1, math.factorial(N - m))
                assert Wb == W, (S, states, Wb, W)
            if W:
                nonzero_units += 1
            hist[W] = hist.get(W, 0) + 1
            if W > best:
                best, best_cfg = W, (S, states)

print(f'N={N} m={m}: W_m(N) = max_k sum_T p_T = {best} ({float(best):.4f}); '
      f'C(N,m) = {math.comb(N, m)}; bound s_N >= {float(math.comb(N, m) / best) if best else "inf":.4f}')
print('  argmax (S, states):', best_cfg)
print('  units with W>0:', nonzero_units,
      ' top of histogram:', sorted(hist.items(), key=lambda kv: -kv[0])[:6])
