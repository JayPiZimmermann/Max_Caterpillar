#!/usr/bin/env python3
"""Per-unit locality weights for general tree units (branch h4-trees).

A unit is abstracted to (n, F, kappa): vertices 0..n-1, hinge forest F,
kappa_o = h_o + #{j > o : (o,j) in M} (slope of the preactivation in x_o when
x_o is above all hinge neighbours).  For a tie set T, |T| = m:
  (s) every t in T without hinge neighbour in T has kappa_t != 0,
  (a) every o outside T has exactly kappa_o hinge neighbours above it
      (T counts as above; outside vertices ordered by a uniformly random order).
w_m(u) = sum_{T, |T|=m, (s)} Pr[(a)]  =  #{rho passing (a),(s)} / (m! (N-m)!).
The exponential theorem needs w_m(u) <= C^m.
Exact rational arithmetic.
"""
from fractions import Fraction
from math import factorial
import itertools

def key_to_unit(key):
    h, M = key
    n = len(h)
    kappa = list(h)
    nbr = [0] * n
    for i, j in M:
        kappa[i] += 1
        nbr[i] |= 1 << j; nbr[j] |= 1 << i
    return n, nbr, kappa

def count_orders(n, nbr, kappa, Tmask):
    out = [o for o in range(n) if not Tmask >> o & 1]
    for o in out:
        if kappa[o] < 0: return 0
    cnt = {Tmask: 1}
    for _ in range(len(out)):
        new = {}
        for placed, c in cnt.items():
            for o in out:
                if placed >> o & 1: continue
                if bin(nbr[o] & placed).count('1') == kappa[o]:
                    k = placed | 1 << o
                    new[k] = new.get(k, 0) + c
        cnt = new
        if not cnt: return 0
    return sum(cnt.values())

def weights(n, nbr, kappa, mmin=0):
    """w[m] for m = 0..n as Fractions; also the list of passing (T, count)."""
    w = [Fraction(0)] * (n + 1)
    for Tmask in range(1 << n):
        m = bin(Tmask).count('1')
        if m < mmin: continue
        ok = True
        for t in range(n):
            if Tmask >> t & 1 and not (nbr[t] & Tmask) and kappa[t] == 0:
                ok = False; break
        if not ok: continue
        c = count_orders(n, nbr, kappa, Tmask)
        if c: w[m] += Fraction(c, factorial(n - m))
    return w
