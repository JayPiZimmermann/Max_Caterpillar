"""Quotient rank of path-unit families mod A, and rank of the unimodal matrix."""
import numpy as np, itertools, sys
from rank import rank_mod, evalA0
from rank_grid import grid

def path_fn(path, apex, X):
    v = X[:, path[-1]] - X[:, apex]
    for a, b in zip(path, path[1:]):
        v = v + np.maximum(X[:, a] - X[:, b], 0)
    return np.maximum(v, 0)

def fam_rank(N, fam, X):
    A = evalA0(N, X)
    F = np.array([path_fn(p, a, X) for a, p in fam], dtype=np.int64)
    return rank_mod(np.vstack([A, F]).T.copy()) - rank_mod(A.T.copy())

def unimodal(w):
    k = w.index(max(w))
    return all(w[i] < w[i+1] for i in range(k)) and all(w[i] > w[i+1] for i in range(k, len(w)-1))

if __name__ == "__main__":
    N = int(sys.argv[1]); R = int(sys.argv[2])
    X = grid(N, R)
    lab = list(range(1, N))
    fixed_both = [(0, list(p) + [N-1]) for p in itertools.permutations(range(1, N-1))]
    fixed_apex = [(0, list(p)) for p in itertools.permutations(lab)]
    allp = [(a, list(p)) for a in range(N) for p in itertools.permutations([i for i in range(N) if i != a])]
    print("N", N, "R", R, "pts", len(X))
    print(" apex0,end fixed:", len(fixed_both), fam_rank(N, fixed_both, X))
    print(" apex0:", len(fixed_apex), fam_rank(N, fixed_apex, X))
    print(" all:", len(allp), fam_rank(N, allp, X))
    # unimodal matrix on S_{N-1}
    perms = list(itertools.permutations(range(N-1)))
    M = np.array([[1 if unimodal([t[p[i]] for i in range(N-1)]) else 0 for p in perms] for t in perms], dtype=np.int64)
    print(" unimodal matrix rank:", rank_mod(M), "of", len(perms))
