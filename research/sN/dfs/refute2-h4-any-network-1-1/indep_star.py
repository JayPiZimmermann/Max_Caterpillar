# Independent exact recomputation: evaluate sigma(g(x)) at the corner points of the
# delta-box at p_L (T tied at 0, outside o at -B^{rho(o)}), compute the k-th mixed
# difference directly from the network function, no braidlib.
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations
from math import ceil, log2
relu=lambda v: v if v>0 else 0
def stars(N):
    bits=max(1,ceil(log2(N-1))); fam=[]
    for c in range(N-2):
        others=[o for o in range(N) if o!=c]
        for b in range(bits):
            fam.append((c,{o:(1 if (r>>b)&1 else -1) for r,o in enumerate(others)}))
    return fam
def g(x,c,s): return sum(so*relu(x[o]-x[c]) for o,so in s.items())
N=int(sys.argv[1]); B=Fr(10); d=Fr(1,1000)
fam=stars(N); print("N",N,"neurons",len(fam),"(N-2)*ceil(log2(N-1)) =",(N-2)*max(1,ceil(log2(N-1))))
for k in range(3,N+1):
    tot=cov=0; minabs=None
    for T in combinations(range(N),k):
        O=[o for o in range(N) if o not in T]
        for perm in permutations(range(1,len(O)+1)):
            tot+=1
            base=[Fr(0)]*N
            for o,r in zip(O,perm): base[o]=-B**r
            ok=False
            for c,s in fam:
                D=Fr(0)
                for r in range(k+1):
                    for S in combinations(T,r):
                        x=list(base)
                        for t in S: x[t]+=d
                        D+=(-1)**(k-r)*relu(g(x,c,s))
                if D!=0:
                    ok=True; a=abs(D)/d
                    minabs=a if minabs is None else min(minabs,a); break
            cov+=ok
    print(" k",k,"localities",tot,"covered",cov,"min|Lambda|/delta",minabs,flush=True)
