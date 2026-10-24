#!/usr/bin/env python3
"""Origin-anchored symmetric MD tests with a prescribed value set (patterns = multisets of size m).
Usage: twin_vals.py m R v1,v2,... [twin|two]"""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from twin_lib import SymTests, eval_germ, rank_mod_p
import sym_md
m, R = int(sys.argv[1]), int(sys.argv[2]); vals = [int(x) for x in sys.argv[3].split(',')]
sym_md.MODE['pred'] = sym_md.two_outleaves if (len(sys.argv) > 4 and sys.argv[4] == 'two') else sym_md.twin_leaves
fam = sym_md.family(m, R)
pats = list(itertools.combinations_with_replacement(vals, m))
T = SymTests(m, pats)
A = np.array([T.vec(lambda Z, v=v, F=F: eval_germ(v, F, Z)) for v, F in fam]).T
b = T.vec(lambda Z: Z.max(axis=1))
r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, b[:, None]], 1))
print(f'm={m} R={R} vals={vals}: {len(fam)} germs, {len(pats)} tests, rank {r1}, with max {r2} ->', 'SEPARATED' if r2 > r1 else 'not', flush=True)
