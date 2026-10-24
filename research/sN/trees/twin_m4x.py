import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from twin_lib import SymTests, eval_germ, orbit
from twin_extract import minimal, solve
vals = [int(x) for x in sys.argv[1].split(',')]; K = 30; m = 4
pats = list(itertools.combinations_with_replacement(vals, m))
T = SymTests(m, pats)
cols = [T.vec(lambda Z, k=k: eval_germ((-1, 1 - 2 * k, k, k), [(2, 1), (3, 1)], Z)) for k in range(-K, K + 1)]
A = np.array(cols).T; b = T.vec(lambda Z: Z.max(axis=1))
idx = minimal(A, b)
c = solve(A, b, idx)
for i, ci in zip(idx, c): print(pats[i], ci, 'orbit', len(orbit(pats[i])), 'Tmax', b[i])
