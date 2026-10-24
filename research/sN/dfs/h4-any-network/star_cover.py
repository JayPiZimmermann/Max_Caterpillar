"""Cap construction: for each centre c, stars g = sum_o s_o sigma(x_o - x_c) with sign codes
s in {+1,-1}; check that together they pass every 3-locality (Lambda* with SOME ray, and
the centered mixed difference)."""
import sys
from math import ceil, log2
from lamstar import *
N = int(sys.argv[1]); m = 3
bits = max(1, ceil(log2(N-1)))
covered_star = set(); covered_mixed = set(); count = 0
for c in range(N):
    others = [o for o in range(N) if o != c]
    for b in range(bits):
        s = {o: (1 if (k >> b) & 1 else -1) for k, o in enumerate(others)}
        # g = sum_o s_o sigma(x_o - x_c); sigma(x_o - x_c) for o<c is a pair (o,c) hinge,
        # for o>c use sigma(x_o-x_c) = sigma(x_c-x_o) + x_o - x_c.
        w = {}; a = [Fr(0)]*N
        for o in others:
            if o < c: w[(o, c)] = s[o]
            else: w[(c, o)] = s[o]; a[o] += s[o]; a[c] -= s[o]
        kappa = [a[o] + sum(w.get((o, j), 0) for j in range(o+1, N)) for o in range(N)]
        th = theta_from(N, w, kappa); count += 1
        covered_star |= set(passes(N, m, th, "star"))
        covered_mixed |= set(passes(N, m, th, "mixed"))
tot = len(list(localities(N, m)))
print("N", N, "neurons", count, "localities", tot, "covered(Lambda* some ray)", len(covered_star), "covered(mixed diff)", len(covered_mixed))
