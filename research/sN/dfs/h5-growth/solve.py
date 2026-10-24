"""Exact feasibility / solutions for supports K in the kink formulation (kf.py)."""
import numpy as np
import flint

from kf import build


class System:
    def __init__(self, N):
        self.N = N
        self.U, self.groups, self.Dm, self.tD = build(N)
        self.n = len(self.U)
        self.gkeys = list(self.groups)
        # unit -> list of (group index, lam)
        self.ug = [[] for _ in range(self.n)]
        for gi, g in enumerate(self.gkeys):
            for u, lam in self.groups[g].items():
                self.ug[u].append((gi, lam))

    def matrix(self, K, srows=None):
        K = list(K)
        SR = list(range(self.Dm.shape[0])) if srows is None else list(srows)
        gis = sorted({gi for u in K for gi, _ in self.ug[u]})
        gpos = {g: r for r, g in enumerate(gis)}
        nS = len(SR)
        A = [[0] * (len(K) + 1) for _ in range(len(gis) + nS)]
        for c, u in enumerate(K):
            for gi, lam in self.ug[u]:
                A[gpos[gi]][c] = lam
            for s in range(nS):
                A[len(gis) + s][c] = int(self.Dm[SR[s], u])
        for s in range(nS):
            A[len(gis) + s][len(K)] = int(self.tD[SR[s]])
        return A

    def solve(self, K, srows=None):
        """Return dict u->Fraction coefficients (some solution) or None."""
        from fractions import Fraction
        K = list(K)
        if not K:
            return None
        A = self.matrix(K, srows)
        M = flint.fmpq_mat(A)
        R, rk = M.rref()
        m = len(K)
        # check consistency: no pivot in last column
        piv = []
        for i in range(rk):
            row = [R[i, j] for j in range(m + 1)]
            j = next(j for j in range(m + 1) if row[j] != 0)
            if j == m:
                return None
            piv.append((i, j))
        sol = {}
        for i, j in piv:
            v = R[i, m]
            sol[K[j]] = Fraction(int(v.p), int(v.q))
        return sol

    def feasible(self, K, srows=None):
        return self.solve(K, srows) is not None


def verify_on_cells(N, units, coeffs):
    """Independent exact check through scripts/vocabulary_search.verify_relation
    (fine cells of the arrangement, exact rationals); aux coefficients solved there."""
    import vocabulary_search as vs
    from fractions import Fraction
    keys = [k for k in units if coeffs.get(k, 0)]
    aux = vs.aux_functions(N)
    funcs = [('key', k) for k in keys] + [('aux', a) for a in aux] + [('max',)]
    # find aux coefficients: solve exactly using kernel_certificate machinery
    return vs, funcs, keys


P = 2147483629


def _nm(A, cols):
    M = flint.nmod_mat(len(A), cols, P)
    for i, row in enumerate(A):
        for j in range(cols):
            if row[j]:
                M[i, j] = row[j] % P
    return M


def feasible_modp(sys_, K, srows=None):
    """Heuristic (mod P) feasibility; certify with System.solve afterwards."""
    K = list(K)
    if not K:
        return False
    A = sys_.matrix(K, srows)
    m = len(K)
    return _nm(A, m).rank() == _nm(A, m + 1).rank()


def prune(sys_, K, srows=None, order=None):
    """Greedy removal while feasible (mod P), then exact solve; returns (K, sol) or None."""
    K = list(K)
    if not feasible_modp(sys_, K, srows):
        return None
    for u in (order if order is not None else sorted(K, key=lambda u: -len(sys_.ug[u]))):
        if u not in K:
            continue
        K2 = [v for v in K if v != u]
        if feasible_modp(sys_, K2, srows):
            K = K2
    sol = sys_.solve(K, srows)
    if sol is None:
        return None
    K = [u for u in K if sol.get(u, 0) != 0]
    return K, sol
