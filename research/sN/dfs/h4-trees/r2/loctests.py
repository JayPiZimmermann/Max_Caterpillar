#!/usr/bin/env python3
"""Exact locality test vectors for the general tree vocabulary (branch h4-trees, round 2).

A locality class is (T, order of the outside labels); the paper's mixed difference
Delta_rho depends only on that class.  We evaluate Delta_rho U_k EXACTLY with integers:
base point p_o = -K*B^(pos) (pos = m, m+1, ... for outside labels in order), cube side 1,
which is the paper's functional scaled by K (positive homogeneity), K, B > c_k.
Returned values are normalised so that Delta(max_N) = 1 on every class.
"""
import itertools, sys
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/dfs/h4-trees')
import treeclass as tc

def relu(t):
    return t if t > 0 else 0

def A(key, x):
    h, M = key
    return sum(hi * xi for hi, xi in zip(h, x)) + sum(relu(x[i] - x[j]) for i, j in M)

def classes(N, ms=None):
    out = []
    for m in (ms or range(3, N + 1)):
        for T in itertools.combinations(range(N), m):
            rest = [o for o in range(N) if o not in T]
            for order in itertools.permutations(rest):
                out.append((T, order))
    return out

def delta(key, N, T, order):
    h, M = key
    c = sum(abs(v) for v in h) + 2 * len(M) + 1
    K = B = 4 * c + 4
    p = [0] * N
    for e, o in enumerate(order):
        p[o] = -K * B ** (len(T) + e)
    if A(key, p) != 0:
        return 0
    m = len(T); tot = 0
    for bits in range(1 << m):
        x = list(p)
        for i, t in enumerate(T):
            if bits >> i & 1: x[t] += 1
        tot += (-1) ** (m - bin(bits).count('1')) * relu(A(key, x))
    return tot * (-1) * (-1) ** m      # Delta(max) = -(-1)^m  -> normalise to +1

def maxN_delta(N, T, order):
    m = len(T); tot = 0
    for bits in range(1, 1 << m):
        tot += (-1) ** (m - bin(bits).count('1'))
    return tot * (-1) * (-1) ** m
