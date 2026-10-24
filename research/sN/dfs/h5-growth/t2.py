from solve import System
import numpy as np, sys, collections
N=int(sys.argv[1])
S=System(N)
full=[u for u in range(S.n) if S.Dm[-1,u]!=0]
print('units',S.n,'D_[N]-active',len(full), collections.Counter(S.Dm[-1,full].tolist()))
print('kink groups per unit hist', sorted(collections.Counter(len(S.ug[u]) for u in range(S.n)).items()))
print('kinkgroups per D-active unit', sorted(collections.Counter(len(S.ug[u]) for u in full).items()))
for u in full[:10]: print(S.U[u], len(S.ug[u]))
