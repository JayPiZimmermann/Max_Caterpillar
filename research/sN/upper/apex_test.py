#!/usr/bin/env python3
"""Which apex sets suffice?  apex(k) = coordinate o with h_o = -1 and no pair of
M at o (K2).  Feasibility of max_N in span(units with apex in A, aux) by LP
(floating; a lead only)."""
import itertools, sys
import numpy as np, scipy.sparse as sp
from scipy.optimize import linprog
import fastsys
N = int(sys.argv[1])
S = fastsys.build(N, verbose=False)
units, aux, A = S['units'], S['aux'], S['A'].tocsc()
U, Aa = len(units), len(aux)
b = -A[:, -1].toarray().ravel()
def apexes(k):
    h, M = k
    used = {i for p in M for i in p}
    return [o for o in range(N) if h[o] == -1 and o not in used]
ap = [apexes(k) for k in units]
print('units with !=1 apex:', sum(len(a) != 1 for a in ap))
def feas(cols):
    M = sp.hstack([A[:, cols], A[:, U:U + Aa]]).tocsr()
    r = linprog(np.zeros(M.shape[1]), A_eq=M, b_eq=b, bounds=(None, None), method='highs')
    return r.status == 0
for m in range(1, N + 1):
    Aset = tuple(range(m))
    cols = [i for i in range(U) if set(ap[i]) & set(Aset)]
    print(m, Aset, len(cols), feas(cols), flush=True)
