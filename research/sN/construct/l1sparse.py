"""L1-minimal (weighted by orbit size) symmetric solution of the top system; exact recheck on support."""
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, hstack, csr_matrix
from classify import build
from linalg import solve
from math import factorial
def sparse_top(N, neurons, cost=None):
    types, lin, cross, ell = build(N, neurons)
    nv = len(types)
    rows = list(cross.values()) + [ell]
    M = lil_matrix((len(rows), nv))
    for i, e in enumerate(rows):
        for v, c in e.items(): M[i, v] = c
    M = csr_matrix(M)
    b = np.zeros(len(rows)); b[-1] = 1
    c = np.ones(nv) if cost is None else np.array([cost[t] for t in sorted(types, key=types.get)], dtype=float)
    res = linprog(np.concatenate([c, c]), A_eq=hstack([M, -M]), b_eq=b, bounds=(0, None), method='highs')
    if res.status != 0: return None
    w = res.x[:nv] - res.x[nv:]
    supp = [v for v in range(nv) if abs(w[v]) > 1e-9]
    # exact solve restricted to support
    sub = [{v: e[v] for v in e if v in supp} for e in rows]
    ok, sol, _, _ = solve(sub, [0] * (len(rows) - 1) + [1], nv)
    inv = {v: t for t, v in types.items()}
    return ok, {inv[v]: sol.get(v, 0) for v in supp}, {inv[v]: w[v] for v in supp}
