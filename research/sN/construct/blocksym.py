"""Block-wise symmetric top system (memory-light).  Feed blocks (T, A); then solve LP / modp."""
import numpy as np
from fastsym import ell_weights
class TopSystem:
    def __init__(self, n):
        self.n = n; self.ew = ell_weights(n); self.ell = {}; self.kc = []; self.tc = []; self.vc = []
    def add(self, T, A):
        n = self.n
        D = np.cumsum(A.astype(np.int64), axis=1)[:, :-1]
        pos = (D > 0).any(1); neg = (D < 0).any(1)
        m = pos & ~neg
        ut, inv = np.unique(T[m], return_inverse=True)
        s = np.zeros(len(ut)); np.add.at(s, inv.ravel(), (D[m] @ self.ew).astype(float))
        for t, v in zip(ut, s): self.ell[int(t)] = self.ell.get(int(t), 0.0) + v
        c = pos & neg; Dc = D[c]; Tc = T[c]
        if len(Dc) == 0: return
        g = np.gcd.reduce(np.abs(Dc), axis=1)
        first = Dc[np.arange(len(Dc)), (Dc != 0).argmax(1)]
        sg = np.where(first > 0, 1, -1); K = (Dc * sg[:, None]) // g[:, None]; lam = sg * g
        nl = lam < 0
        if nl.any():
            ut, inv = np.unique(Tc[nl], return_inverse=True)
            s = np.zeros(len(ut)); np.add.at(s, inv.ravel(), ((K[nl] @ self.ew) * lam[nl]).astype(float))
            for t, v in zip(ut, s): self.ell[int(t)] = self.ell.get(int(t), 0.0) + v
        code = np.zeros(len(K), dtype=np.int64)
        for j in range(K.shape[1]): code = code * 128 + (K[:, j] + 64)
        pair = np.stack([code, Tc.astype(np.int64)], 1)
        up, inv = np.unique(pair, axis=0, return_inverse=True)
        vals = np.zeros(len(up), dtype=np.int64); np.add.at(vals, inv.ravel(), np.abs(lam))
        self.kc.append(up[:, 0]); self.tc.append(up[:, 1]); self.vc.append(vals)
    def solve_lp(self, ntypes, cost=None):
        from scipy.optimize import linprog
        from scipy.sparse import coo_matrix, hstack, vstack, csr_matrix
        kc = np.concatenate(self.kc); tc = np.concatenate(self.tc); vc = np.concatenate(self.vc)
        uk, ki = np.unique(kc, return_inverse=True)
        C = coo_matrix((vc.astype(float), (ki.ravel(), tc)), shape=(len(uk), ntypes)).tocsr()
        ell = np.zeros(ntypes)
        for t, v in self.ell.items(): ell[t] = v
        M = vstack([C, csr_matrix(ell.reshape(1, -1))]).tocsr()
        b = np.zeros(M.shape[0]); b[-1] = 1
        del C, kc, tc, vc; self.kc = self.tc = self.vc = None
        if cost is None:
            res = linprog(np.zeros(ntypes), A_eq=M, b_eq=b, bounds=(None, None), method='highs')
            w = None if res.status != 0 else res.x
        else:
            res = linprog(np.concatenate([cost, cost]), A_eq=hstack([M, -M]), b_eq=b, bounds=(0, None), method='highs')
            w = None if res.status != 0 else res.x[:ntypes] - res.x[ntypes:]
        return res.status, w, M.shape
