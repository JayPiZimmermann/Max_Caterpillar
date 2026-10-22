#!/usr/bin/env python3
"""Max over leaf patterns of the stretch weight sum (cubic-bound inequality).

Stretch s_1..s_k, leaf counts c_j in {0, 1, 2 (meaning >= 2)}.
Edge-type T (case kappa_a = -1 only):
  spine edge (s_j, s_{j+1}) needs c_j = c_{j+1} = 0, weight 1/((j-1)! (k-j-1)!)
  leaf edge  (s_j, leaf)    needs c_j = 1,            weight 1/((j-1)! (k-j)!)
Vertex-type T (case with a second negative vertex): x = s_j with c_j = 0,
  weight 1/((j-1)! (k-j)!)  (computed separately).
"""
import itertools
from fractions import Fraction
from math import factorial as f
worst_e = worst_v = 0
for k in range(1, 15):
    for c in itertools.product((0, 1, 2), repeat=k):
        s = Fraction(0)
        for j in range(1, k + 1):
            if c[j - 1] == 1: s += Fraction(1, f(j - 1) * f(k - j))
            if j < k and c[j - 1] == 0 and c[j] == 0: s += Fraction(1, f(j - 1) * f(k - j - 1))
        worst_e = max(worst_e, s)
    v = sum(Fraction(1, f(j - 1) * f(k - j)) for j in range(1, k + 1))
    worst_v = max(worst_v, v)
print('max edge-type sum', worst_e, ' max vertex-type sum', worst_v)
