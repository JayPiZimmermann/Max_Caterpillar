import sys, pickle, numpy as np
from core import units_of
from sparse_form import build
from fastmodp import rref
N = int(sys.argv[1])
U = units_of(N)
gkeys, Kink, Ss, Dm, tD = build(N, U)
A = np.vstack([Kink, Dm])
b = np.concatenate([np.zeros(len(Kink), dtype=np.int64), tD])
R, piv = rref(A)
R2, piv2 = rref(np.hstack([A, b[:, None]]))
print('N', N, 'rank [Kink;D]', len(piv), 'with target', len(piv2))
np.savez_compressed(f'data/sparse_{N}.npz', Kink=Kink, Dm=Dm, tD=tD)
pickle.dump((gkeys, Ss), open(f'data/sparse_keys_{N}.pkl', 'wb'))
