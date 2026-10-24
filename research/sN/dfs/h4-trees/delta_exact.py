#!/usr/bin/env python3
"""Exact m-th mixed difference Delta_rho U of a unit at a locality (branch h4-trees).

Same functional as the paper (app:count-exponential): base point p_o = 0 on the
tie set T (positions < m), p_o = -B^{rho(o)} otherwise; Delta = sum over corners
of the delta-cube in the T coordinates with signs.  Exact integer/Fraction
arithmetic.  B, delta chosen from the unit as in the paper.
"""
from fractions import Fraction
import itertools

def relu(t):
    return t if t > 0 else 0

def eval_key(key, x):
    h, M = key
    return relu(sum(a * b for a, b in zip(h, x)) + sum(relu(x[i] - x[j]) for i, j in M))

def params(key):
    h, M = key
    c = sum(abs(t) for t in h) + 2 * len(M)
    return Fraction(1, c + 1), c + 2       # delta, B

def delta(key, order, m, dl=None, B=None):
    """order: list of labels by position (position 0 = highest)."""
    N = len(order)
    d0, B0 = params(key)
    dl = dl or d0; B = B or B0
    p = [0] * N
    for pos, o in enumerate(order):
        p[o] = 0 if pos < m else -B ** pos
    T = order[:m]
    tot = Fraction(0)
    for r in range(m + 1):
        for S in itertools.combinations(T, r):
            x = list(p)
            for t in S: x[t] += dl
            tot += (-1) ** (m - r) * eval_key(key, x)
    return tot
