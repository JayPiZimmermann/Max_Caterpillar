import time,numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, vstack
from solve import System
S=System(5); n=S.n
rows, cols, vals = [], [], []
for r, g in enumerate(S.gkeys):
    for u, lam in S.groups[g].items():
        rows.append(r); cols.append(u); vals.append(lam)
Kink = csr_matrix((vals, (rows, cols)), shape=(len(S.gkeys), n), dtype=float)
A = vstack([Kink, csr_matrix(S.Dm[-1:].astype(float))]).tocsr()
b = np.zeros(A.shape[0]); b[-1]=1
t=time.time()
r=linprog(np.ones(2*n),A_eq=hstack([A,-A]).tocsr(),b_eq=b,bounds=(0,None),method='highs-ipm')
print(r.status,r.fun,time.time()-t, (np.abs(r.x)>1e-7).sum())
