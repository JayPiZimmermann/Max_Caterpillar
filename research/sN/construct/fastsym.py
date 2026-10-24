"""Fast symmetric top test.  Input: integer arrays T (type ids, int64) and A (n columns, int64),
one row per labeled neuron in the identity chamber.  Returns (TOP?, ncross, ntypes)."""
import numpy as np
from math import comb
from modp import rank_mod, P as PR
def ell_weights(n):
    w = np.zeros(n - 1, dtype=np.int64)
    for r in range(1, n + 1):
        c = (-1) ** (r - 1) * comb(n - 1, r - 1)
        if r - 1 < n - 1: w[r - 1] += c
        if r - 2 >= 0: w[r - 2] -= c
    return w
def top_test_fast(n, T, A, return_system=False):
    D = np.cumsum(A, axis=1)[:, :-1]
    pos = (D > 0).any(1); neg = (D < 0).any(1)
    ew = ell_weights(n)
    ntypes = int(T.max()) + 1
    ell = np.zeros(ntypes, dtype=object)
    # one-signed positive: contributes D
    m = pos & ~neg
    contrib = D[m] @ ew
    np.add.at(ell, T[m], contrib.astype(object))
    # crossing
    c = pos & neg
    Dc = D[c]; Tc = T[c]
    g = np.gcd.reduce(np.abs(Dc), axis=1)
    first = Dc[np.arange(len(Dc)), (Dc != 0).argmax(1)]
    sg = np.where(first > 0, 1, -1)
    K = (Dc * sg[:, None]) // g[:, None]
    lam = sg * g
    # linear part for lam<0: lam*K
    neg_l = lam < 0
    np.add.at(ell, Tc[neg_l], ((K[neg_l] @ ew) * lam[neg_l]).astype(object))
    # cross classes
    keys, kid = np.unique(K, axis=0, return_inverse=True)
    kid = kid.ravel()
    pair = kid.astype(np.int64) * ntypes + Tc
    up, inv = np.unique(pair, return_inverse=True)
    vals = np.zeros(len(up), dtype=np.int64); np.add.at(vals, inv.ravel(), np.abs(lam))
    rows = up // ntypes; cols = up % ntypes
    ur, ri = np.unique(rows, return_inverse=True)
    C = np.zeros((len(ur), ntypes), dtype=np.int64)
    C[ri.ravel(), cols] = vals % PR
    L = np.array([[int(v) % PR for v in ell]], dtype=np.int64)
    if return_system: return C, ell
    r1 = rank_mod(C) if len(ur) else 0
    r2 = rank_mod(np.vstack([C, L]))
    return r2 > r1, len(ur), ntypes

def top_lp(n, T, A, cost=None):
    """LP: min cost.|w| s.t. crossing rows = 0, ell.w = 1 (floats, HiGHS). Returns (status, w)."""
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix, hstack, vstack, csr_matrix
    D = np.cumsum(A, axis=1)[:, :-1]
    pos = (D > 0).any(1); neg = (D < 0).any(1)
    ew = ell_weights(n); ntypes = int(T.max()) + 1
    ell = np.zeros(ntypes)
    m = pos & ~neg
    np.add.at(ell, T[m], (D[m] @ ew).astype(float))
    c = pos & neg; Dc = D[c]; Tc = T[c]
    g = np.gcd.reduce(np.abs(Dc), axis=1)
    first = Dc[np.arange(len(Dc)), (Dc != 0).argmax(1)]
    sg = np.where(first > 0, 1, -1); K = (Dc * sg[:, None]) // g[:, None]; lam = sg * g
    nl = lam < 0
    np.add.at(ell, Tc[nl], ((K[nl] @ ew) * lam[nl]).astype(float))
    keys, kid = np.unique(K, axis=0, return_inverse=True); kid = kid.ravel()
    C = coo_matrix((np.abs(lam).astype(float), (kid, Tc)), shape=(len(keys), ntypes)).tocsr()
    M = vstack([C, csr_matrix(ell.reshape(1, -1))]).tocsr()
    b = np.zeros(M.shape[0]); b[-1] = 1
    cc = np.ones(ntypes) if cost is None else cost
    res = linprog(np.concatenate([cc, cc]), A_eq=hstack([M, -M]), b_eq=b, bounds=(0, None), method='highs')
    if res.status != 0: return res.status, None, M.shape
    return 0, res.x[:ntypes] - res.x[ntypes:], M.shape
