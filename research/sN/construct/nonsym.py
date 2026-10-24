"""Non-symmetric sparse search: labeled neurons (l, W) on n vars; LP min L1 subject to
crossing cancellation in all chambers and top = 1 (top via T_k = sum_S (-1)^{|S|+1} sigma(q_k(S)))."""
import itertools
import numpy as np
from fractions import Fraction as Fr
from scipy.sparse import coo_matrix, hstack
from scipy.optimize import linprog

def qval(n, l, W, S):
    v = sum(l[i] for i in S)
    for (i, j), w in W.items():
        if i in S and j not in S: v += w
    return v

def top_coef(n, l, W):
    t = 0
    for k in range(n + 1):
        for S in itertools.combinations(range(n), k):
            q = qval(n, l, W, set(S))
            if q > 0: t += (-1) ** (k + 1) * q
    return t

def rows_for(n, neurons):
    """returns dict (chamber, key) -> {k: coef}"""
    rows = {}
    chains = list(itertools.permutations(range(n)))
    for k, (l, W) in enumerate(neurons):
        for ci, ch in enumerate(chains):
            S = set(); D = []
            for p in range(n - 1):
                S.add(ch[p]); D.append(qval(n, l, W, S))
            if any(d > 0 for d in D) and any(d < 0 for d in D):
                first = next(d for d in D if d)
                key = tuple(Fr(d, abs(first)) for d in D)
                if first < 0: key = tuple(-x for x in key)
                e = rows.setdefault((ci, key), {}); e[k] = e.get(k, 0) + abs(first)
    return rows

def solve_sparse(n, neurons, iters=6, verbose=True):
    rows = rows_for(n, neurons)
    T = np.array([float(top_coef(n, l, W)) for l, W in neurons])
    R = list(rows.values()); m = len(neurons)
    I = [i for i, e in enumerate(R) for _ in e]; J = [k for e in R for k in e]; V = [float(c) for e in R for c in e.values()]
    A = coo_matrix((V + list(T), (I + [len(R)] * m, J + list(range(m)))), shape=(len(R) + 1, m)).tocsr()
    b = np.zeros(len(R) + 1); b[-1] = 1
    wts = np.ones(m); best = None
    for it in range(iters):
        res = linprog(np.concatenate([wts, wts]), A_eq=hstack([A, -A]), b_eq=b, bounds=(0, None), method='highs')
        if res.status != 0:
            if verbose: print('LP status', res.status, res.message); return None
        x = res.x[:m] - res.x[m:]
        supp = np.nonzero(np.abs(x) > 1e-9)[0]
        if verbose: print('iter', it, 'support', len(supp), flush=True)
        if best is None or len(supp) < len(best[0]): best = (supp, x)
        wts = 1.0 / (np.abs(x) + 1e-4)
    return best, rows, T

def exact_rows(n, neurons):
    """Equations for sum_k w_k sigma(g_k) + sum_i b_i x_i + sum_{i<j} c_ij m_ij = max_n, all chambers.
    Variables: neurons 0..m-1, then b (n), then c (C(n,2)).  Returns list of (dict, rhs)."""
    m = len(neurons); pairs = list(itertools.combinations(range(n), 2))
    eqs = {}
    chains = list(itertools.permutations(range(n)))
    for ci, ch in enumerate(chains):
        pos = {e: p for p, e in enumerate(ch)}
        lin = [dict() for _ in range(n)]   # coefficient of x_e
        cross = {}
        for k, (l, W) in enumerate(neurons):
            a = [Fr(v) for v in l]
            for (i, j), w in W.items():
                if pos[i] < pos[j]: a[i] += w; a[j] -= w
            S = set(); D = []; s = Fr(0)
            for p in range(n - 1):
                s += a[ch[p]]; D.append(s)
            assert s + a[ch[n - 1]] == 0
            P_ = any(d > 0 for d in D); N_ = any(d < 0 for d in D)
            if P_ and not N_:
                for e in range(n):
                    if a[e]: lin[e][k] = lin[e].get(k, 0) + a[e]
            elif P_ and N_:
                first = next(d for d in D if d)
                key = tuple(d / abs(first) for d in D)
                if first < 0:
                    key = tuple(-x for x in key)
                    for e in range(n):
                        if a[e]: lin[e][k] = lin[e].get(k, 0) + a[e]
                c = cross.setdefault(key, {}); c[k] = c.get(k, 0) + abs(first)
        for key, c in cross.items(): eqs[('c', ci, key)] = (c, 0)
        for e in range(n):
            d = dict(lin[e]); d[m + e] = 1
            for pi, (i, j) in enumerate(pairs):
                hi = i if pos[i] < pos[j] else j
                if hi == e: d[m + n + pi] = 1
            eqs[('l', ci, e)] = (d, 1 if pos[e] == 0 else 0)
    return list(eqs.values()), m + n + len(pairs)

def solve_sparse_exact(n, neurons, iters=6, verbose=True):
    eqs, nv = exact_rows(n, neurons); m = len(neurons)
    I = [i for i, (d, r) in enumerate(eqs) for _ in d]; J = [k for d, r in eqs for k in d]; V = [float(c) for d, r in eqs for c in d.values()]
    A = coo_matrix((V, (I, J)), shape=(len(eqs), nv)).tocsr(); b = np.array([float(r) for d, r in eqs])
    wts = np.concatenate([np.ones(m), 1e-6 * np.ones(nv - m)]); best = None
    for it in range(iters):
        res = linprog(np.concatenate([wts, wts]), A_eq=hstack([A, -A]), b_eq=b, bounds=(0, None), method='highs')
        if res.status != 0:
            print('LP status', res.status, res.message); return None
        x = res.x[:nv] - res.x[nv:]
        supp = [k for k in range(m) if abs(x[k]) > 1e-9]
        if verbose: print('iter', it, 'neurons', len(supp), flush=True)
        if best is None or len(supp) < len(best[0]): best = (supp, x)
        wts = np.concatenate([1.0 / (np.abs(x[:m]) + 1e-4), 1e-6 * np.ones(nv - m)])
    return best
