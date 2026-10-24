# Independent recheck of chamber-cancellation on r2_spec_N5_k4 (read only).
import sys, itertools, random
from fractions import Fraction as Fr
sys.path.insert(0,'/home/jzimmermann/code/Max_Caterpillar/research/sN/dfs/h4-general-neurons')
import r2_spec_N5_k4 as S
N=S.N; relu=lambda t: t if t>0 else 0
def ev(lin,pairs,x): return sum(Fr(a)*xi for a,xi in zip(lin,x))+sum(Fr(w)*relu(x[i]-x[j]) for (i,j),w in pairs.items())
# 1. identity check at random rational points
bad=0
for _ in range(20000):
    x=[Fr(random.randint(-50,50),random.randint(1,7)) for _ in range(N)]
    v=ev(*S.R,x)+sum(Fr(d)*relu(ev(l,p,x)) for d,l,p in S.NEURONS)
    bad+= v!=max(x)
print('identity failures',bad)
# 2. per chamber: coefficient vectors projected orthogonally to 1; group by proportionality
ok=True; nch=0; cnt={}
for perm in itertools.permutations(range(N)):
    pos={v:r for r,v in enumerate(perm)}
    groups=[]
    for k,(d,l,p) in enumerate(S.NEURONS):
        c=[Fr(t) for t in l]
        for (i,j),w in p.items():
            if pos[i]<pos[j]: c[i]+=w; c[j]-=w
        assert sum(c)==0
        # sign change in open chamber: c not identically zero and not of one sign on rays
        rays=[[1 if pos[v]<m else 0 for v in range(N)] for m in range(1,N)]
        vals=[sum(a*b for a,b in zip(c,r)) for r in rays]
        if not(any(v>0 for v in vals) and any(v<0 for v in vals)): continue
        cnt[k]=cnt.get(k,0)+1
        for g in groups:
            r0=g[0]; idx=next(i for i in range(N) if r0[i]!=0); lam=c[idx]/r0[idx]
            if all(c[i]==lam*r0[i] for i in range(N)): g[1]+=Fr(d)*abs(lam); break
        else: groups.append([c,Fr(d)])
    if groups: nch+=1
    ok &= all(g[1]==0 for g in groups)
print('chambers with crossings',nch,'cancellation',ok,'per-neuron',cnt)
