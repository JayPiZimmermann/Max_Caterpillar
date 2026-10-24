"""Faster local-condition machinery (numpy, arithmetic mod a 25-bit prime).

Same mathematics as germs.py: V_loc(S) = {f in W : germ_x0(f) in germ_x0(V)
for x0 in S}; we compute the rank of all local conditions restricted to W.
Rank mod p is a lower bound of the rational rank of the condition matrix;
dimension equalities are re-checked with a second prime.
"""
import itertools
import random
from math import gcd

import numpy as np

from ambient import Ambient, unit_kink_sets, units_of, cell_data, base_funcs
from hyperplanes import global_hyperplanes

PR = 33554393


def rref(A, p):
    A = np.array(A, dtype=np.int64) % p
    m, n = A.shape
    piv, r = [], 0
    for c in range(n):
        if r == m:
            break
        nz = np.flatnonzero(A[r:, c])
        if nz.size == 0:
            continue
        q = r + nz[0]
        if q != r:
            A[[r, q]] = A[[q, r]]
        A[r] = (A[r] * pow(int(A[r, c]), p - 2, p)) % p
        col = A[:, c].copy()
        col[r] = 0
        rows = np.flatnonzero(col)
        if rows.size:
            A[rows] = (A[rows] - (col[rows, None] * A[r][None, :]) % p) % p
        piv.append(c)
        r += 1
    return A[:r], piv


def left_null(G, p):
    """Rows y with y G = 0 (basis), G m x n."""
    m, n = G.shape
    aug = np.concatenate([G % p, np.eye(m, dtype=np.int64)], axis=1)
    R, piv = rref(aug, p)
    # rows of R whose first n entries vanish
    out = [R[i, n:] for i in range(R.shape[0]) if not R[i, :n].any()]
    # rref of [G | I] puts zero-G rows at bottom only if pivots beyond n
    return np.array(out, dtype=np.int64).reshape(len(out), m)


def to_nmod(A, p):
    import flint
    A = np.asarray(A, dtype=np.int64) % p
    return flint.nmod_mat(A.shape[0], A.shape[1], [int(v) for v in A.ravel()], p)


def from_nmod(M):
    return np.array([int(v) for v in M.entries()], dtype=np.int64).reshape(M.nrows(), M.ncols())


def nullspace_cols(C, p):
    """Basis (columns) of {v : C v = 0} mod p (flint)."""
    X, nul = to_nmod(C, p).nullspace()
    return from_nmod(X)[:, :nul]


def rank_big(A, p):
    return to_nmod(A, p).rank()


class Setup:
    def __init__(self, N, p=PR, units=None, D=None):
        self.N, self.p = N, p
        U = units if units is not None else units_of(N)
        self.units = U
        perms, data, D0 = unit_kink_sets(N, U)
        D = D if D is not None else D0
        self.A = A = Ambient(N, D)
        C = A.constraints()
        Cm = np.zeros((len(C), A.nvars), dtype=np.int64)
        for r, row in enumerate(C):
            for c, x in row.items():
                Cm[r, c] = x
        self.BW = nullspace_cols(Cm, p)            # nvars x dimW
        self.dimW = self.BW.shape[1]
        _, bdata = cell_data(N, base_funcs(N))
        vecs = [A.vector(r) for r in data] + [A.vector(r) for r in bdata]
        self.Vrows = vecs
        self.Vmat = np.zeros((A.nvars, len(vecs)), dtype=np.int64)
        for j, v in enumerate(vecs):
            for i, x in v.items():
                self.Vmat[i, j] = x % p
        self.H, self.braid = global_hyperplanes(N, U)

    def eval_row(self, x):
        N, A = self.N, self.A
        pi = tuple(sorted(range(N), key=lambda i: (x[i], i)))
        c = A.pidx[pi]
        t = [x[pi[j]] - x[pi[j - 1]] for j in range(1, N)]
        row = {}
        for j in range(N - 1):
            if t[j]:
                row[A.var_lin(c, j)] = t[j]
        for pp in A.D[c]:
            v = sum(a * b for a, b in zip(pp, t))
            if v > 0:
                row[A.var_kink(c, pp)] = v
        return row

    def local_conditions(self, x0, rng, m0=None, B=100_000, zmax=40):
        N, A, p = self.N, self.A, self.p
        m = m0 or 4 * N * N
        last = -1
        while True:
            rows = []
            for _ in range(m):
                z = [0] + [rng.randint(-zmax, zmax) for _ in range(N - 1)]
                rows.append(self.eval_row([B * a + b for a, b in zip(x0, z)]))
            cols = sorted(set().union(*[set(r) for r in rows]))
            ci = {c: k for k, c in enumerate(cols)}
            E = np.zeros((m, len(cols)), dtype=np.int64)
            for i, r in enumerate(rows):
                for c, x in r.items():
                    E[i, ci[c]] = x % p
            GW = (E @ self.BW[cols]) % p
            _, pv = rref(GW, p)
            rW = len(pv)
            if rW == last or rW < m // 2:
                break
            last = rW
            m *= 2
        Vloc = self.Vmat[cols]
        nzc = np.flatnonzero(Vloc.any(axis=0))
        GV = (E @ Vloc[:, nzc]) % p
        _, pvv = rref(GV.T, p) if GV.size else (None, [])
        rV = len(pvv)
        if rW == rV:
            return np.zeros((0, self.dimW), dtype=np.int64), rW, rV
        Y = left_null(GV, p)
        cond = (Y @ GW) % p
        R, _ = rref(cond, p)
        return R, rW, rV


def rays(N, hyps):
    """All rays (x_0 = 0 normalization, primitive, both signs) of the central
    arrangement given by forms `hyps` (a . 1 = 0) on R^N / R1."""
    Y = np.array([h[1:] for h in hyps], dtype=np.int64)
    n = N - 1
    out = set()
    for combo in itertools.combinations(range(len(Y)), n - 1):
        M = Y[list(combo)]
        # generalized cross product: signed maximal minors
        w = []
        for k in range(n):
            sub = np.delete(M, k, axis=1)
            w.append(((-1) ** k) * int(round(np.linalg.det(sub))) if n > 2 else None)
        if not any(w):
            continue
        g = 0
        for a in w:
            g = gcd(g, abs(a))
        w = tuple(a // g for a in w)
        out.add(w)
        out.add(tuple(-a for a in w))
    return sorted((0,) + w for w in out)


def canon(x0):
    """Canonical rep of a ray up to coordinate permutation and translation."""
    best = None
    for perm in itertools.permutations(range(len(x0))):
        y = [x0[perm[i]] for i in range(len(x0))]
        y = tuple(a - y[0] for a in y)
        if best is None or y < best:
            best = y
    return best
