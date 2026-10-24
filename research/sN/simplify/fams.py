"""Quotient ranks of sub-families of path-face functions (apex 0, end b=N-1)."""
import numpy as np, itertools, sys
from rank import rank_mod, evalA0
from rank_grid import grid

def face(path, apex, states, X):
    v = X[:, path[-1]] - X[:, apex]
    for (a, b), s in zip(zip(path, path[1:]), states):
        d = X[:, a] - X[:, b]
        if s == 1: v = v + d
        elif s == 2: v = v + np.maximum(d, 0)
    return np.maximum(v, 0)

def qrank(N, F, X):
    A = evalA0(N, X)
    return rank_mod(np.vstack([A, np.array(F, dtype=np.int64)]).T.copy()) - rank_mod(A.T.copy())

if __name__ == "__main__":
    N = int(sys.argv[1]); R = int(sys.argv[2]); X = grid(N, R)
    b = N - 1
    mids = list(itertools.permutations(range(1, N - 1)))
    for name, S in [("hinge/linear", (1, 2)), ("all 3 states", (0, 1, 2))]:
        F = [face(list(p) + [b], 0, st, X) for p in mids for st in itertools.product(S, repeat=N - 2)]
        print(N, name, len(F), qrank(N, F, X), flush=True)
    apex0 = [face(list(p), 0, st, X) for p in itertools.permutations(range(1, N)) for st in itertools.product((0,1,2), repeat=N-2)]
    print(N, "apex0 paths all states", len(apex0), qrank(N, apex0, X), flush=True)
