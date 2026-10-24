import sys, numpy as np, flint, time
from solve import System
N=int(sys.argv[1]); S=System(N)
P=2147483629
rows=[]
for gi,g in enumerate(S.gkeys):
    rows.append(S.groups[g])
M=flint.nmod_mat(len(rows), S.n, P)
for r,g in enumerate(rows):
    for u,l in g.items(): M[r,u]=l
t=time.time(); rk=M.rank(); print('N',N,'units',S.n,'kink rank',rk,'kernel dim',S.n-rk, time.time()-t)
# rank with D rows
nS=S.Dm.shape[0]
M2=flint.nmod_mat(len(rows)+nS, S.n, P)
for r,g in enumerate(rows):
    for u,l in g.items(): M2[r,u]=l
for s in range(nS):
    for u in range(S.n): M2[len(rows)+s,u]=int(S.Dm[s,u])%P
print('rank with D rows', M2.rank())
