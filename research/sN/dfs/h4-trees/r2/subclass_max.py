#!/usr/bin/env python3
"""Exact per-unit maxima w_m = max_k #{locality classes of size m with Delta != 0}/(N-m)!
for subclasses of the tree vocabulary (apex-0 keys only; symmetric).  Usage: subclass_max.py N mode
mode in: in (generators towards head vertex), out (away from head vertex), star, G."""
import sys, math
import loctests as L
N, mode = int(sys.argv[1]), sys.argv[2]
cls = L.classes(N)
keys = sorted(k for k in L.tc.vocabulary(N, mode) if k[0][0] == -1 and all(0 not in e for e in k[1]))
best = {}
for k in keys:
    cnt = {}
    for T, o in cls:
        if L.delta(k, N, T, o): cnt[len(T)] = cnt.get(len(T), 0) + 1
    for m, c in cnt.items():
        if c > best.get(m, (0,))[0]: best[m] = (c, k)
print(f'N={N} mode={mode}: {len(keys)} apex-0 keys')
for m in sorted(best):
    c, k = best[m]
    print(f'  m={m}: w_m = {c / math.factorial(N - m):g}  (C(N-2,m-2) = {math.comb(N - 2, m - 2)})  key h={k[0]} M={sorted(k[1])}')
