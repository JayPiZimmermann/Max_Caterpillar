#!/usr/bin/env python3
"""Are the out-star and in-star top units in V_N (caterpillar span)? (h4-trees)
out-star: relu(x_c - x_a + sum_l relu(x_l - x_c))   (centre is the tail of every generator; violates P1)
in-star : relu(x_c - x_a + sum_l relu(x_c - x_l))   (P1 holds)
Usage: python star_in_V.py N"""
import sys
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs
import treeclass as tc
N = int(sys.argv[1])
K0, _ = vs.dictionary(N)
base = [('key', k) for k in sorted(K0) if not vs.is_auxiliary(k)] + [('aux', a) for a in vs.aux_functions(N)]
r0, ok0 = vs.exact_rank_fast(N, base)
print(f'N={N}: dim V_N = {r0} [{ok0}]')
for name, hin in [('out', lambda l, c: (l, c)), ('in', lambda l, c: (c, l))]:
    a, c = 0, 1
    k = tc.norm(N, [(c, a)], [hin(l, c) for l in range(N) if l not in (a, c)])
    r1, ok1 = vs.exact_rank_fast(N, base + [('key', k)])
    print(f'  {name}-star (apex {a}, centre {c}) key {k[0]} {sorted(k[1])}: in V_N: {r1 == r0} [{ok1}]; in K0: {k in K0}')
