#!/usr/bin/env python3
"""Is max_N in span(star units + auxiliary functions)?  (branch h4-trees)

Star unit with apex a and centre c (all other labels are leaves, edges oriented
leaf - centre, head e_c - e_a):
    S_{a,c}(x) = relu(x_c - x_a + sum_{l != a,c} relu(x_l - x_c)).
Uses scripts/vocabulary_search.exact_expansion: mod-p kernel lifted to rationals
and verified exactly on every cell of the braid arrangement (with 0).
Usage: python star_span.py N
"""
import sys, itertools
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs
from fractions import Fraction

def norm_key(N, head, hinges):
    """head: list of (i,j,coef) linear terms coef*(x_i-x_j); hinges: (i,j) meaning relu(x_i-x_j)."""
    h = [0]*N; M = set()
    for i, j, c in head:
        h[i] += c; h[j] -= c
    for i, j in hinges:
        if i > j:
            h[i] += 1; h[j] -= 1; i, j = j, i
        M.add((i, j))
    return (tuple(h), frozenset(M))

def star_unit(N, a, c):
    return norm_key(N, [(c, a, 1)], [(l, c) for l in range(N) if l not in (a, c)])

if __name__ == '__main__':
    N = int(sys.argv[1])
    units = [star_unit(N, a, c) for a in range(N) for c in range(N) if a != c]
    res = vs.exact_expansion(N, units)
    if res is None:
        print(f'N={N}: max_N NOT in span of {len(units)} star units + aux (exact)')
    else:
        d, e = res
        nz = {k: v for k, v in d.items() if v}
        print(f'N={N}: max_N IN span; {len(nz)} star units with nonzero coefficient')
        for k, v in nz.items(): print('  ', k, v)
        print('  aux:', {k: v for k, v in e.items() if v})
