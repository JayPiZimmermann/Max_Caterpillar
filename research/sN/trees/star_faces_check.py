#!/usr/bin/env python3
"""Faces of the rooted-star pyramids of Brunck et al. (M = empty):
conv(0, e_c - e_a + sum_l [0, e_c - e_l]).  Check which normalized face keys are
caterpillar face keys (scripts/vocabulary_search.dictionary).  Usage: star_faces_check.py N"""
import sys, itertools
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/dfs/h4-trees')
import vocabulary_search as vs
from treeclass import norm
N = int(sys.argv[1])
K0, _ = vs.dictionary(N)
bad = []; tot = 0
for a in range(N):
    for c in range(N):
        if a == c: continue
        leaves = [l for l in range(N) if l not in (a, c)]
        for st in itertools.product(['o', 'l', 'h'], repeat=len(leaves)):
            lin = [(c, a)] + [(c, l) for l, s in zip(leaves, st) if s == 'l']
            hin = [(c, l) for l, s in zip(leaves, st) if s == 'h']
            key = norm(N, lin, hin)
            tot += 1
            if key not in K0 and not vs.is_auxiliary(key):
                bad.append((a, c, st))
print(f'N={N}: {tot} star faces; not caterpillar faces (and not auxiliary): {len(bad)}')
from collections import Counter
print(Counter(tuple(sorted(s)) for _,_,s in bad))
