"""Families: for each apex a, units (a, rho.c.b(a)) for all orders of the
other N-2 labels (diagonal family of the original argument per apex).
Square matrix against detectors ({a,b(a),c}, rho). Report rank / acyclicity."""
import itertools, sys, numpy as np
from rank import rank_mod
from lam import unit
from tri_helpers import lamT
N = int(sys.argv[1])
for name, bf in [("b=a+1", lambda a: (a + 1) % N), ("b=N-1 (a<N-1), b=0 for a=N-1", lambda a: N - 1 if a != N - 1 else 0)]:
    idx = []
    for a in range(N):
        b = bf(a)
        for p in itertools.permutations([i for i in range(N) if i not in (a, b)]):
            idx.append((a, b, list(p)))
    def det(a, b, p, f):
        return lamT(N, (a, b, p[-1]), p[:-1], f)
    M_ = np.array([[det(a, b, p, lambda x, a2=a2, b2=b2, p2=p2: unit(a2, p2 + [b2], x)) for (a2, b2, p2) in idx] for (a, b, p) in idx], dtype=np.int64)
    n = len(idx)
    print(N, name, "size", n, "rank", rank_mod(M_), "offdiag", int((M_ != 0).sum() - (np.diag(M_) != 0).sum()), flush=True)
