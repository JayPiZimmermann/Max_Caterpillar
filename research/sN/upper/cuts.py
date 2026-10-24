#!/usr/bin/env python3
"""Cover cuts from tie functionals (research/sN/upper/cuts.py).

For p in Z^N with a triple T = {a, b, c} tied at the top value s and all other
coordinates <= s - 1, the six-point functional
    Lam g = J g(q+) - J g(q-),  q± = p ± eps (e_a + e_b),
    J g(q) = g(q + del d) + g(q - del d) - 2 g(q),  d = e_a - e_b,
with eps = 1/(8C), del = eps/2, C >= 1 + max_k sum|h| + 2N, kills every
auxiliary function and every linear function and gives Lam max_N = 2 del
(NOTE.md, steps 1-2; the outside coordinates do not move on the stencil, so
their relative order is irrelevant).  Hence every expansion contains a unit k
with Lam U_k != 0:   sum_{k : Lam U_k != 0} z_k >= 1   (a valid cover cut).
Evaluations are exact (integers after scaling by 16 C).
"""
import itertools

import numpy as np


def relu(t):
    return t if t > 0 else 0


def unit_val(key, y):
    h, M = key
    return relu(sum(a * b for a, b in zip(h, y)) + sum(relu(y[i] - y[j]) for i, j in M))


def max_val(y):
    return max(y)


def lam(g, p, a, b, C, N):
    """Exact Lam g * (16 C) evaluated at integer points scaled by 16C."""
    S = 16 * C                     # eps*S = 2, del*S = 1
    P = [S * t for t in p]
    def pt(sa, sb):
        y = list(P)
        y[a] += sa
        y[b] += sb
        return y
    def J(sgn):
        e = 2 * sgn
        return g(pt(e + 1, e - 1)) + g(pt(e - 1, e + 1)) - 2 * g(pt(e, e))
    return J(1) - J(-1)


def tie_points(N, svals=(0,), depth=3, extra_random=0, seed=0):
    """Integer points: T tied at s, outside coordinates in s-1 .. s-depth."""
    rng = np.random.default_rng(seed)
    out = []
    for s in svals:
        for T in itertools.combinations(range(N), 3):
            rest = [o for o in range(N) if o not in T]
            for vals in itertools.product(range(1, depth + 1), repeat=len(rest)):
                p = [s] * N
                for o, v in zip(rest, vals):
                    p[o] = s - v
                for c in T:                       # c = the fixed member
                    a, b = [t for t in T if t != c]
                    out.append((tuple(p), a, b))
    return out


def pass_sets(N, units, points):
    C = 1 + max(sum(abs(t) for t in k[0]) for k in units) + 2 * N
    sets = []
    for p, a, b in points:
        assert lam(max_val, p, a, b, C, N) == 2, 'Lam max_N must be 2 del'
        S = frozenset(i for i, k in enumerate(units)
                      if lam(lambda y: unit_val(k, y), p, a, b, C, N) != 0)
        sets.append(S)
    return sets


def minimal_sets(sets):
    uniq = sorted(set(sets), key=len)
    keep = []
    for S in uniq:
        if not any(K <= S for K in keep):
            keep.append(S)
    return keep
