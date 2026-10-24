"""Feasibility tests in the sparse formulation (see sparse_form.py)."""
import numpy as np
from fastmodp import rref


class SparseSpace:
    def __init__(self, N):
        d = np.load(f'data/sparse_{N}.npz')
        self.N = N
        self.Kink, self.Dm, self.tD = d['Kink'], d['Dm'], d['tD']
        self.A = np.vstack([self.Kink, self.Dm])
        self.b = np.concatenate([np.zeros(len(self.Kink), dtype=np.int64), self.tD])
        self.n = self.A.shape[1]

    def sub(self, K):
        K = list(K)
        Ak = self.A[:, K]
        rows = np.flatnonzero(np.any(Ak != 0, axis=1) | (self.b != 0))
        return Ak[rows], self.b[rows]

    def feasible(self, K):
        """mod-P test: b in span A[:,K] (search lead)."""
        if not len(K):
            return False
        Ak, bk = self.sub(K)
        _, p1 = rref(Ak)
        _, p2 = rref(np.hstack([Ak, bk[:, None]]))
        return len(p1) == len(p2)

    def prune(self, K, order=None):
        K = list(K)
        for k in (order if order is not None else list(K)):
            K2 = [x for x in K if x != k]
            if self.feasible(K2):
                K = K2
        return K
