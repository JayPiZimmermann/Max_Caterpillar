#!/usr/bin/env python3
"""Given a test matrix A (patterns x germs) and max vector b, find a minimal pattern subset that still
separates and print the rational functional (normalised Lambda(max) = 1)."""
import numpy as np
from fractions import Fraction
from twin_lib import rank_mod_p, left_kernel_frac


def separates(A, b, idx):
    if not idx:
        return False
    M = A[idx]; bb = b[idx][:, None]
    return rank_mod_p(M) < rank_mod_p(np.concatenate([M, bb], 1))


def minimal(A, b, order=None):
    idx = list(range(A.shape[0])) if order is None else list(order)
    assert separates(A, b, idx)
    for i in list(idx):
        t = [j for j in idx if j != i]
        if separates(A, b, t):
            idx = t
    return idx


def solve(A, b, idx):
    # independent columns only, to keep Fractions small
    M = A[idx]
    ker = left_kernel_frac(M)          # c with c M = 0
    for c in ker:
        val = sum(ci * int(bi) for ci, bi in zip(c, b[idx]))
        if val != 0:
            return [ci / val for ci in c]
    return None
