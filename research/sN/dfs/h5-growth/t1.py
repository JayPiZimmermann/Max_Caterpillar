from solve import System
import numpy as np, sys
N=int(sys.argv[1])
S=System(N)
kf=[u for u in range(S.n) if not S.ug[u]]
print('kinkfree',len(kf), 'feasible with kinkfree only:', S.feasible(kf))
for u in kf: print(S.U[u], S.Dm[:,u].tolist())
print('all feasible', S.feasible(range(S.n)) if N<=4 else '')
