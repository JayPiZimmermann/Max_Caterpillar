#!/usr/bin/env python3
"""Local sparsity of max_m in the germ class (research/sN/rank/local.py).

Quotient matrix: exact cell coordinates on R^m (scripts/vocabulary_search.cell_blocks)
of germs, auxiliary functions and max_m, row reduced modulo P with the auxiliary
columns eliminated first.  The remaining rows restricted to germ/max columns form a
matrix Q with: a combination of germs equals max_m modulo aux iff Q d = Q_max
(on the rationals; modulo P we obtain search leads, decisive claims are re-checked
with exact rational arithmetic in certify()).
"""
import sys
import itertools
from fractions import Fraction
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs

P = vs.P


def full_matrix(m, germs):
    aux = vs.aux_functions(m)
    funcs = [('aux', a) for a in aux] + [('key', g) for g in germs] + [('max',)]
    rows = []
    for block in vs.cell_blocks(m, funcs):
        rows.extend(block)
    A = np.zeros((len(rows), len(funcs)), dtype=object)
    for i, row in enumerate(rows):
        for j, c in row.items():
            A[i, j] = c
    return A, len(aux)


def quotient_modp(A, naux):
    R, piv = vs.rref_mod_p(np.array(A, dtype=np.int64))
    keep = [i for i, c in enumerate(piv) if c >= naux]
    return R[keep][:, naux:] % P          # columns: germs..., max


def rank_p(M):
    if M.shape[1] == 0 or M.shape[0] == 0:
        return 0
    R, piv = vs.rref_mod_p(M)
    return len(piv)


def in_span(Q, S):
    """max (last column) in span of columns S modulo aux (mod P)."""
    sub = Q[:, list(S)]
    return rank_p(np.hstack([sub, Q[:, -1:]])) == rank_p(sub)


def exact_rank(M):
    """Exact rank over Q of an integer/object matrix by fraction Gaussian elimination."""
    A = [[Fraction(int(x)) for x in row] for row in M]
    r = 0
    ncol = len(A[0]) if A else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c] / A[r][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
    return r


def certify_excluded(A, naux, S):
    """Exact: max not in span(aux + germs S)."""
    cols = list(range(naux)) + [naux + s for s in S]
    B = A[:, cols]
    Bm = A[:, cols + [A.shape[1] - 1]]
    return exact_rank(Bm) > exact_rank(B)
