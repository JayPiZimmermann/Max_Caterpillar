#!/usr/bin/env python3
"""Exact Q_C(r) on abstract spine components (research/sN/polytope/longspine.py).
Component data: spine length L, lambda_1 >= -1, lambda_j >= 0 (j >= 2), leaf counts a_j.
Q_C(r) = sum_X r^{sum_{X}(1+lam+a) + sum_{not X} lam} prod_runs hook(run), with the
validity rules of spinecheck.py (verified there against brute force for N <= 8).
DP over 'last X position'.  Reports max Q over lam in {-1..2}x{0..2}^{L-1},
a_1, a_L in {0,1}, other a_j = 0.  Usage: longspine.py r_num r_den Lmax"""
import itertools, sys
from fractions import Fraction as F

r = F(int(sys.argv[1]), int(sys.argv[2])); Lmax = int(sys.argv[3])


def runw(lam, a, i, j, root_in):
    """weight of outside run i..j-1 (0-based), or 0 if invalid"""
    mins = []
    for v in range(i, j):
        if v == 0:
            if lam[0] == 0: mins.append(v)
            elif lam[0] != -1: return 0
        else:
            if lam[v] == 1: mins.append(v)
            elif lam[v] != 0: return 0
    if len(mins) != 1:
        return 0
    m = mins[0]
    w = F(1)
    for v in range(i, j):
        # leaves of v hang above v (h = 1 each)
        if v < m: h = sum(1 + a[u] for u in range(i, v + 1))
        elif v > m: h = sum(1 + a[u] for u in range(v, j))
        else: h = sum(1 + a[u] for u in range(i, j))
        w /= h
    return w * r ** sum(lam[i:j])


def Q(lam, a):
    L = len(lam)
    kap = [a[j] + (1 if j < L - 1 else 0) + lam[j] for j in range(L)]
    # f[j] = total weight of prefixes 0..j with j in X ; handle (b) for X vertices with kappa 0
    tot = F(0)
    f = {}
    for j in range(L):
        xw = r ** (1 + lam[j] + a[j])
        acc = runw(lam, a, 0, j, True) if j > 0 else F(1)   # all before j outside (one run)
        # (b) for j: kappa 0 needs an S-neighbour (leaves are S if a>0, but kappa 0 => a=0)
        for i in range(j):
            acc += f[i] * (runw(lam, a, i + 1, j, False) if i + 1 < j else 1)
        f[j] = acc * xw
    # validity of (b): recompute by brute force-lite: kappa-0 X vertices need X neighbour.
    return f


def Qfull(lam, a):
    L = len(lam)
    kap = [a[j] + (1 if j < L - 1 else 0) + lam[j] for j in range(L)]
    total = F(0)
    for mask in range(1 << L):
        X = [j for j in range(L) if mask >> j & 1]
        if any(lam[j] >= 2 and not mask >> j & 1 for j in range(L)):
            continue
        if any(kap[j] == 0 and not ((j > 0 and mask >> (j - 1) & 1) or (j < L - 1 and mask >> (j + 1) & 1)) for j in X):
            continue
        w = r ** sum(1 + lam[j] + a[j] for j in X)
        j = 0
        while j < L and w:
            if mask >> j & 1:
                j += 1; continue
            k = j
            while k < L and not mask >> k & 1:
                k += 1
            w *= runw(lam, a, j, k, j == 0)
            j = k
        total += w
    return total


best = {}
for L in range(1, Lmax + 1):
    bv, barg = F(0), None
    for lam in itertools.product(*([(-1, 0, 1, 2)] + [(0, 1, 2)] * (L - 1))):
        for a1 in (0, 1):
            for aL in ((0, 1) if L > 1 else (None,)):
                a = [0] * L; a[0] = a1
                if L > 1: a[-1] = aL
                if L == 1 and a1 == 0:
                    continue
                D = sum(lam)
                q = Qfull(list(lam), a)   # already includes r^{sum lam} = r^D
                if q > bv:
                    bv, barg = q, (lam, a)
    print(f'r={r} L={L}: max Q = {bv} ({float(bv):.4f}) at lam={barg[0]} a={barg[1]}', flush=True)
