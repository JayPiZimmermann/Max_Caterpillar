#!/usr/bin/env python3
"""Shared helpers for the twin-germ elimination study (research/sN/trees, steps 13+).
Germ G(v, F)(z) = relu(<v,z> + sum_{(i,j) in F} relu(z_i - z_j)) on R^m (F oriented: term relu(z_i-z_j)).
MD_delta f = sum_{S subset [m]} (-1)^{m-|S|} f(delta_S) (box at the origin, steps delta > 0).
Symmetric test T_p f = sum_{delta in S_m-orbit of p} MD_delta f.
"""
import itertools
from fractions import Fraction
import numpy as np

P = 2147483629


def eval_germ(v, F, Z):
    s = Z @ np.array(v, dtype=np.int64)
    for i, j in F:
        s = s + np.maximum(Z[:, i] - Z[:, j], 0)
    return np.maximum(s, 0)


def orbit(p):
    return sorted(set(itertools.permutations(p)))


class SymTests:
    def __init__(self, m, pats):
        self.m = m
        self.pats = pats
        cube = np.array(list(itertools.product([0, 1], repeat=m)), dtype=np.int64)
        self.sign = np.array([(-1) ** (m - int(s.sum())) for s in cube], dtype=np.int64)
        blocks = [np.array(orbit(p), dtype=np.int64) for p in pats]
        self.sizes = [len(b) for b in blocks]
        allD = np.concatenate(blocks)
        self.nd = len(allD)
        self.Z = (allD[:, None, :] * cube[None, :, :]).reshape(-1, m)
        self.idx = np.repeat(np.arange(len(pats)), self.sizes)
        self.ncube = len(cube)

    def vec(self, fn):
        vals = fn(self.Z).reshape(self.nd, self.ncube) @ self.sign
        return np.bincount(self.idx, weights=vals, minlength=len(self.pats)).round().astype(np.int64)


def rank_mod_p(A):
    A = np.array(A, dtype=np.int64) % P
    m, n = A.shape
    r = 0
    for c in range(n):
        if r == m:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy(); col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            A[nzr] = (A[nzr] - (col[nzr, None] * A[r][None, :]) % P) % P
        r += 1
    return r


def left_kernel_frac(A):
    """rational basis of {c : c A = 0} for a small integer matrix A (rows = tests)."""
    M = [[Fraction(int(x)) for x in row] for row in np.array(A).T]  # cols of A as rows: solve M c = 0
    n = len(M[0]) if M else 0
    piv = []; r = 0
    for col in range(n):
        pr = next((k for k in range(r, len(M)) if M[k][col] != 0), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        pv = M[r][col]; M[r] = [x / pv for x in M[r]]
        for k in range(len(M)):
            if k != r and M[k][col] != 0:
                f = M[k][col]; M[k] = [x - f * y for x, y in zip(M[k], M[r])]
        piv.append(col); r += 1
    free = [c for c in range(n) if c not in piv]
    basis = []
    for fc in free:
        c = [Fraction(0)] * n; c[fc] = Fraction(1)
        for k, pc in enumerate(piv):
            c[pc] = -M[k][fc]
        basis.append(c)
    return basis
