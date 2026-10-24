"""Plain numpy mod-P elimination (P < 2^31, so products fit in int64)."""
import numpy as np
from core import P


def rref(A, stop_rank=None):
    """Reduced row echelon form mod P; returns (R, pivot columns)."""
    A = np.array(A, dtype=np.int64) % P
    m, n = A.shape
    piv, r = [], 0
    for c in range(n):
        if r == m or (stop_rank is not None and r == stop_rank):
            break
        col = A[r:, c]
        nz = np.flatnonzero(col)
        if nz.size == 0:
            continue
        p = r + nz[0]
        if p != r:
            A[[r, p]] = A[[p, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r, c:] = (A[r, c:] * inv) % P
        colv = A[:, c].copy()
        colv[r] = 0
        rows = np.flatnonzero(colv)
        if rows.size:
            A[np.ix_(rows, np.arange(c, n))] = (A[np.ix_(rows, np.arange(c, n))]
                                               - np.outer(colv[rows], A[r, c:]) % P) % P
        piv.append(c)
        r += 1
    return A[:r], piv
