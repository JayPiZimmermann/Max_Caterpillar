"""Local (germ) conditions for V^TI_N inside the ambient W_N.

For a point x0 (mod 1) a *local functional at x0* is a linear combination of
point evaluations f(B x0 + z), |z| small, chosen so that every hyperplane of the
global arrangement (braid + kink) that does not contain x0 keeps its sign on
all evaluation points.  A local functional that vanishes on V^TI_N is a local
condition.  V_loc(S) := {f in W_N : every local condition at every x0 in S
holds}.  Always V <= V_loc(S) <= W.  All arithmetic mod a prime p.
"""
import itertools
import random
import sys
import time

import flint

from ambient import Ambient, unit_kink_sets, units_of, cell_data, base_funcs
from hyperplanes import global_hyperplanes

P1 = 2_147_483_629


def nm(rows, ncols, p):
    M = flint.nmod_mat(len(rows), ncols, p)
    for r, row in enumerate(rows):
        for c, x in row.items():
            M[r, c] = x % p
    return M


def relu(t):
    return t if t > 0 else 0


class Setup:
    def __init__(self, N, p=P1, extra_funcs=()):
        self.N, self.p = N, p
        U = units_of(N)
        self.units = U
        perms, data, D = unit_kink_sets(N, U)
        self.A = A = Ambient(N, D)
        C = A.constraints()
        Cm = nm(C, A.nvars, p)
        X, nul = Cm.nullspace()
        # basis of W: first `nul` columns of X  (nvars x nul)
        self.dimW = nul
        self.BW = flint.nmod_mat(A.nvars, nul, p)
        for i in range(A.nvars):
            for j in range(nul):
                self.BW[i, j] = X[i, j]
        _, bdata = cell_data(N, base_funcs(N))
        vecs = [A.vector(r) for r in data] + [A.vector(r) for r in bdata]
        self.Vrows = vecs
        self.Vmat = nm(vecs, A.nvars, p).transpose()     # nvars x nV
        self.dimV = self.Vmat.rank()
        self.H, self.braid = global_hyperplanes(N, U)

    # evaluation row (sparse over ambient variables) at integer point x
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
            v = relu(sum(a * b for a, b in zip(pp, t)))
            if v:
                row[A.var_kink(c, pp)] = v
        return row

    def local_points(self, x0, m, rng, B=10_000, zmax=25):
        N = self.N
        pts = []
        for _ in range(m):
            z = [0] + [rng.randint(-zmax, zmax) for _ in range(N - 1)]
            pts.append([B * a + b for a, b in zip(x0, z)])
        return pts

    def local_conditions(self, x0, rng, m0=40):
        """Rows (over the W basis) of the local conditions at x0, and the germ
        dimensions (dim germ W, dim germ V)."""
        N, A, p = self.N, self.A, self.p
        m = m0
        last = -1
        while True:
            pts = self.local_points(x0, m, rng)
            E = nm([self.eval_row(x) for x in pts], A.nvars, p)
            GW = E * self.BW
            rW = GW.rank()
            if rW == last or rW < m // 2:
                break
            last = rW
            m *= 2
        GV = E * self.Vmat
        rV = GV.rank()
        Y, k = GV.transpose().nullspace()      # columns y with GV^T y = 0
        Yk = flint.nmod_mat(k, m, p)
        for i in range(m):
            for j in range(k):
                Yk[j, i] = Y[i, j]
        return Yk * GW, rW, rV


def rays(N, hyps):
    """All rays of the arrangement (x-coords, x_0 = 0 normalization), both signs."""
    import numpy as np
    from fractions import Fraction
    Y = [h[1:] for h in hyps]              # forms in y = (x_1-x_0, ...)
    n = N - 1
    out = set()
    from math import gcd
    for combo in itertools.combinations(range(len(Y)), n - 1):
        M = flint.fmpz_mat([list(Y[i]) for i in combo])
        X, nul = M.nullspace()
        if nul != 1:
            continue
        w = [int(X[i, 0]) for i in range(n)]
        g = 0
        for a in w:
            g = gcd(g, abs(a))
        w = tuple(a // g for a in w)
        out.add(w)
        out.add(tuple(-a for a in w))
    return sorted((0,) + w for w in out)
