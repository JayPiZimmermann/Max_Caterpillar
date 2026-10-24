#!/usr/bin/env python3
"""Test closure of a candidate invariant polytope for child summaries (h4-trees).
P = {(sigma,gamma,omega,alpha) >= 0 : J-constraints}.  Since the parent summary is
multilinear in the children, extremes are attained at vertex tuples.
"""
import itertools, sys
from fractions import Fraction as Fr
import numpy as np
x = Fr(1, 2)

def parent(e, kids):
    pa = Fr(1); ps = Fr(1); pa_ = Fr(1)
    for (s, g, w, a) in kids: pa *= a; ps *= s; pa_ *= (s + w)
    if e >= 2:
        sg = x ** (1 + e) * pa; return (sg, Fr(0), Fr(0), sg)
    if e == 1:
        sg = pa / 4; c0 = ps; call = pa_
        return (sg, call / 2, Fr(0), sg + x * (c0 + call) / 2)
    if not kids:
        return (Fr(0), Fr(0), Fr(1), x)          # leaf e=0: s*=x, o0=1
    c0 = Fr(0); call = Fr(0)
    for k, (s, g, w, a) in enumerate(kids):
        r0 = Fr(1); r1 = Fr(1)
        for j, (s2, g2, w2, a2) in enumerate(kids):
            if j != k: r0 *= s2; r1 *= (s2 + w2)
        c0 += g * r0; call += g * r1
    sg = pa / 2
    return (sg, call / 2, (ps + pa_) / 2, sg + x * (c0 + call) / 2)

def final(e, kids):
    s, g, w, a = parent(e, kids)
    # F = s/x + (c0+call)/2 ; recompute c0, call:
    if e >= 2: return s / x
    if e == 1:
        ps = Fr(1); pa_ = Fr(1)
        for (s_, g_, w_, a_) in kids: ps *= s_; pa_ *= (s_ + w_)
        return s / x + (ps + pa_) / 2
    c0 = Fr(0); call = Fr(0)
    for k, (s_, g_, w_, a_) in enumerate(kids):
        r0 = Fr(1); r1 = Fr(1)
        for j, (s2, g2, w2, a2) in enumerate(kids):
            if j != k: r0 *= s2; r1 *= (s2 + w2)
        c0 += g_ * r0; call += g_ * r1
    return s / x + (c0 + call) / 2

def solve(M):
    n = len(M)
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] != 0), None)
        if piv is None: return None
        M[c], M[piv] = M[piv], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [M[r][j] - f * M[c][j] for j in range(n + 1)]
    return tuple(M[i][n] / M[i][i] for i in range(n))

def vertices(A, b):
    """Vertices of {z in R^4 : A z <= b} by brute-force 4-subsets of constraints."""
    V = set()
    n = len(A)
    for idx in itertools.combinations(range(n), 4):
        z = solve([[Fr(A[i][j]) for j in range(4)] + [Fr(b[i])] for i in idx])
        if z is None: continue
        if all(sum(Fr(A[i][j]) * z[j] for j in range(4)) <= b[i] for i in range(n)):
            V.add(z)
    return sorted(V)

def check(A, b, kmax):
    V = vertices(A, b)
    print(len(V), 'vertices:', [tuple(map(str, v)) for v in V])
    ok = True
    def inP(z): return all(sum(Fr(A[i][j]) * z[j] for j in range(4)) <= b[i] for i in range(len(A)))
    worstF = Fr(0)
    for e in (0, 1, 2):
        for k in range(0, kmax + 1):
            for kids in itertools.combinations_with_replacement(V, k):
                z = parent(e, list(kids))
                if not inP(z):
                    print('  NOT CLOSED: e', e, 'kids', kids, '->', z); ok = False
                    break
                if k >= 2:
                    F = final(e, list(kids)); worstF = max(worstF, F)
    print('closed up to k =', kmax, ':', ok, ' max final F (k>=2) =', worstF)
    return ok

if __name__ == '__main__':
    # variables (sigma, gamma, omega, alpha)
    A = [[-1,0,0,0],[0,-1,0,0],[0,0,-1,0],[0,0,0,-1],
         [1,0,0,1],          # J1 alpha + sigma <= 1
         [1,1,1,0],          # J2 sigma + omega + gamma <= 1
         [0,Fr(1,2),0,1]]    # J3 alpha + gamma/2 <= 1
    b = [0,0,0,0,1,1,1]
    check(A, b, int(sys.argv[1]) if len(sys.argv) > 1 else 3)
