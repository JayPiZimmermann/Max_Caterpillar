"""EXACT: linear (not covering) form of the locality method restricted to star neurons.
For a star (c,s), Lambda_L sigma(g)/delta depends only on T (D below; 0 if c not in T),
and Lambda_L max/delta = (-1)^(k+1).  Test whether the target vector over all T, |T|>=3,
lies in the span of (a) the covering family of r2_star_check.py, (b) all {+1,-1} stars,
(c) all {+1,-1,0} stars.  Exact rank over Q via sympy.
Usage: python r2_star_linear.py N"""
import sys
from itertools import combinations, product
from math import ceil, log2
from braidlib import rref
def rank(rows): return len(rref(rows)[0]) if rows else 0

def D(T, c, s):
    if c not in T: return 0
    U = [t for t in T if t != c]; k = len(T); tot = 0
    for r in range(len(U) + 1):
        for S in combinations(U, r):          # G(1_S) = sum_{t in S} s_t if c not in S, else 0
            val = sum(s[t] for t in S)
            tot += (-1) ** (k - r) * max(val, 0)
    return tot

N = int(sys.argv[1])
Ts = [T for k in range(3, N + 1) for T in combinations(range(N), k)]
target = [(-1) ** (len(T) + 1) for T in Ts]
def fam_codes(vals):
    F = []
    for c in range(N):
        others = [o for o in range(N) if o != c]
        for code in product(vals, repeat=N - 1):
            F.append((c, dict(zip(others, code))))
    return F
bits = max(1, ceil(log2(N - 1)))
cover = []
for c in range(N - 2):
    others = [o for o in range(N) if o != c]
    for b in range(bits):
        cover.append((c, {o: (1 if (k >> b) & 1 else -1) for k, o in enumerate(others)}))
for name, F in [("cover", cover), ("pm1", fam_codes([1, -1])), ("pm1_0", fam_codes([1, -1, 0]))]:
    cols = [[D(T, c, s) for T in Ts] for (c, s) in F]   # rank of column set = rank of these rows
    r0 = rank(cols); r1 = rank(cols + [target])
    print("N", N, name, "stars", len(F), "rows(T)", len(Ts), "rank", r0, "rank+target", r1,
          "IN SPAN" if r0 == r1 else "NOT in span", flush=True)
