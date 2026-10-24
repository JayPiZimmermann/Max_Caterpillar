import pickle,sys
from solve import System
import itertools
N=4; S=System(N)
d=pickle.load(open('data/milp_4_4_0_top.pkl','rb'))
perms=list(itertools.permutations(range(N)))
for k,c in d['d'].items():
    u=S.U.index(k)
    print(k,c,'D',S.Dm[:,u].tolist(),'kinks',[(perms[S.gkeys[g][0]],S.gkeys[g][1],l) for g,l in S.ug[u]])
