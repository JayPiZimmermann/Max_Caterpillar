"""Mod-P cut generation: hyperplanes of the quotient avoiding max.

A cut is a set C of units such that some linear functional y on the quotient
(span of units and max modulo aux) has y(max) != 0 and supp(y on units) = C.
Every expansion of max_N must use a unit of C.  (Mod-P computations here are
*search leads*; certify.py recomputes each cut over Q.)
"""
import numpy as np, flint
from core import P, unit_perm_table
from modp import nm


def hyperplane_cut(G, t, order):
    """Greedy: B = greedy basis of the contraction by t in the given order,
    y = functional with y(B) = 0, y(t) = 1.  Returns (y, cut indices)."""
    q = G.shape[0]
    M = np.hstack([t[:, None], G[:, order]])
    R, rk = nm(M).rref()
    R = np.array(R.tolist(), dtype=np.int64)
    piv = [int(np.nonzero(R[i])[0][0]) for i in range(rk)]
    assert piv[0] == 0
    B = [order[c - 1] for c in piv[1:]]
    if len(B) < q - 1:
        # units of order do not span: complete with remaining units
        rest = [u for u in range(G.shape[1]) if u not in set(order)]
        return hyperplane_cut(G, t, list(order) + rest)
    A = np.hstack([G[:, B], t[:, None]]).T  # q x q
    rhs = np.zeros(q, dtype=np.int64); rhs[-1] = 1
    y = nm(A).solve(nm(rhs))
    y = np.array([int(y[i, 0]) for i in range(q)], dtype=np.int64)
    vals = (nm(y[None, :]) * nm(G))
    vals = np.array([int(vals[0, j]) for j in range(G.shape[1])])
    return y, np.nonzero(vals)[0]


def orbit(cut, T):
    return {frozenset(int(x) for x in T[p][list(cut)]) for p in range(T.shape[0])}
