"""Mod-P feasibility tests in the quotient coordinates (G, t) and exact lifting."""
import numpy as np, flint
from fractions import Fraction
from core import P, rational_reconstruct, verify_expansion, aux_list


def nm(A):
    A = np.asarray(A, dtype=np.int64) % P
    if A.ndim == 1:
        A = A[:, None]
    return flint.nmod_mat(A.shape[0], A.shape[1], [int(v) for v in A.ravel()], P)


class Space:
    def __init__(self, N):
        d = np.load(f'data/space_{N}.npz')
        self.N = N
        self.G = d['G'] % P
        self.t = d['t'] % P
        self.EU, self.EA, self.Em, self.S = d['EU'], d['EA'], d['Em'], d['S']
        import pickle
        self.U = pickle.load(open(f'data/units_{N}.pkl', 'rb'))
        self.q, self.n = self.G.shape

    def rank(self, K, with_t=False):
        K = list(K)
        if not K and not with_t:
            return 0
        A = self.G[:, K]
        if with_t:
            A = np.hstack([A, self.t[:, None]])
        return nm(A).rank()

    def feasible(self, K):
        """Mod-P test: t in span G[:,K] (heuristic; confirm with exact())."""
        return self.rank(K) == self.rank(K, True)

    def exact(self, K):
        """Solve exactly on support K (mod P, rational reconstruction) and
        verify the identity on every cell.  Returns (d, e) or None."""
        K = list(K)
        S = self.S
        A = np.hstack([self.EU[S][:, K], self.EA[S]])
        b = self.Em[S]
        # pick independent columns
        M = nm(np.hstack([A, b[:, None]]))
        R, rk = M.rref()
        R = np.array(R.tolist(), dtype=np.int64)
        piv = [int(np.nonzero(R[i])[0][0]) for i in range(rk)]
        if A.shape[1] in piv:
            return None
        sol = [Fraction(0)] * A.shape[1]
        for i, c in enumerate(piv):
            sol[c] = rational_reconstruct(int(R[i, -1]))
        d = {self.U[k]: sol[i] for i, k in enumerate(K) if sol[i] != 0}
        aux = aux_list(self.N)
        e = {aux[j]: sol[len(K) + j] for j in range(len(aux)) if sol[len(K) + j] != 0}
        if verify_expansion(self.N, self.U, d, e):
            return d, e
        return None

    def prune(self, K, order=None):
        """Greedy inclusion-minimal feasible subset (mod-P tests)."""
        K = list(K)
        order = order if order is not None else list(K)
        for k in order:
            K2 = [x for x in K if x != k]
            if self.feasible(K2):
                K = K2
        return K
