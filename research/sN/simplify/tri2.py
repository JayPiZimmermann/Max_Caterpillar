"""Try the 6 role choices (apex, mid, end) = permutation of sorted T for the
monotone unit of detector (T, rho); report rank and acyclicity."""
import itertools, sys, numpy as np
from rank import rank_mod
from lam import unit
from tri_helpers import lamT
N = int(sys.argv[1])
idx = [(T, list(rho)) for T in itertools.combinations(range(N), 3)
       for rho in itertools.permutations([i for i in range(N) if i not in T])]
for roles in itertools.permutations(range(3)):
    def u(T, r):
        a, m, M = (T[roles[0]], T[roles[1]], T[roles[2]])
        return lambda x: unit(a, r + [m, M], x)
    M_ = np.array([[lamT(N, T, rho, u(T2, r2)) for (T2, r2) in idx] for (T, rho) in idx], dtype=np.int64)
    print(N, roles, "rank", rank_mod(M_), "of", len(idx), flush=True)
