import sys, time, numpy as np
from core import units_of
from kinks import kink_groups
from fastmodp import rref
N = int(sys.argv[1])
U = units_of(N)
groups, per_unit = kink_groups(N, U)
Km = np.zeros((len(groups), len(U)), dtype=np.int64)
for r, g in enumerate(groups.values()):
    for u, lam in g.items():
        Km[r, u] = lam
t = time.time()
R, piv = rref(Km)
print('N', N, 'units', len(U), 'kink rows', len(groups), 'rank', len(piv), 'kernel dim', len(U) - len(piv), time.time() - t)
np.save(f'data/kinkmat_{N}.npy', Km)
