#!/usr/bin/env python3
"""Abstract test of the Case I 'one stretch' step WITHOUT caterpillar input.
Leafless hinge path s_1..s_L, intrinsic up-counts t_i in {0,1,2} (as the sketch
allows), D = 1 (sum t = L).  Placement at spine edge (a, a+1) is valid iff the
path has an orientation with s_a, s_{a+1} above their other neighbours and each
other s_i having exactly t_i neighbours above it.  Prints t-vectors with two
valid placements separated by a non-T vertex with t != 1 (so not in one
'stretch of t = 1')."""
import itertools
def valid(t, a):
    L = len(t)
    for x in itertools.product((0, 1), repeat=L - 1):   # x[i]=1: s_{i+1} above s_i (0-based edge i)
        if x[a] is None: pass
        ok = True
        for i in range(L):
            if i in (a, a + 1):
                if i == a and i > 0 and x[i - 1] != 1: ok = False   # s_a above s_{a-1}
                if i == a + 1 and i < L - 1 and x[i] != 0: ok = False  # s_{a+1} above s_{a+2}
                continue
            up = (1 - x[i - 1] if i > 0 else 0) + (x[i] if i < L - 1 else 0)
            if (i - 1 == a and i > 0): up = 1 if i > 0 else 0  # neighbour a+1 in T is above
            if up != t[i]: ok = False
        if ok: return True
    return False
for L in range(3, 8):
    for t in itertools.product((0, 1, 2), repeat=L):
        if sum(t) != L: continue
        V = [a for a in range(L - 1) if valid(t, a)]
        if len(V) >= 2 and any(t[i] != 1 for i in range(min(V), max(V) + 2)):
            print(L, t, 'valid spine edges (0-based a):', V)
