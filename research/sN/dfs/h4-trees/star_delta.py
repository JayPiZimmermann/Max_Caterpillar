#!/usr/bin/env python3
"""Count, exactly, the permutations rho with Delta_rho S_{a,c} != 0 for the star
unit S_{a,c}(x) = relu(x_c - x_a + sum_l relu(x_l - x_c)).  (branch h4-trees)
Prediction: exactly those rho whose tie set contains a and c, i.e.
C(N-2,m-2) m! (N-m)! permutations.
Usage: python star_delta.py N"""
import sys, itertools, math
from delta_exact import delta
from star_span import star_unit
N = int(sys.argv[1])
key = star_unit(N, 0, 1)
for m in range(3, N + 1):
    seen = 0; seen_tie = set(); bad = 0
    for order in itertools.permutations(range(N)):
        if delta(key, list(order), m) != 0:
            seen += 1; seen_tie.add(frozenset(order[:m]))
            if not {0, 1} <= set(order[:m]): bad += 1
    pred = math.comb(N - 2, m - 2) * math.factorial(m) * math.factorial(N - m)
    print(f'N={N} m={m}: seen {seen}, predicted {pred}, tie sets {len(seen_tie)}, '
          f'without {{a,c}}: {bad}; W/(m!(N-m)!) = {seen // (math.factorial(m)*math.factorial(N-m))}', flush=True)
