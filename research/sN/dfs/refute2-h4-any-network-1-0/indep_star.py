"""Independent exact check: evaluate sigma(g) of the actual star neurons at the
corners of a box of side delta at the concrete point p_L (T at 0, outside o at
-B^{r+1}), no germ library.  Also checks centered box.  Usage: python indep_star.py N"""
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations, product
from math import ceil, log2
N=int(sys.argv[1]); B=Fr(10); d=Fr(1,1000)
sig=lambda t: t if t>0 else Fr(0)
bits=max(1,ceil(log2(N-1)))
stars=[]
for c in range(N-2):
    others=[o for o in range(N) if o!=c]
    for b in range(bits):
        stars.append((c,{o:(1 if (r>>b)&1 else -1) for r,o in enumerate(others)}))
g=lambda st,x: sum(s*sig(x[o]-x[st[0]]) for o,s in st[1].items())
def lam(st,T,base,centered):
    k=len(T); tot=Fr(0)
    for eps in product((0,1),repeat=k):
        x=list(base)
        for t,e in zip(T,eps): x[t]+= (e*d - (d/2 if centered else 0))
        tot+=(-1)**(k-sum(eps))*sig(g(st,x))
    return tot
def lam_max(T,base):
    k=len(T); tot=Fr(0)
    for eps in product((0,1),repeat=k):
        x=list(base)
        for t,e in zip(T,eps): x[t]+=e*d
        tot+=(-1)**(k-sum(eps))*max(x)
    return tot
for k in range(3,N+1):
    tot=cov=covc=0; bad=0
    for T in combinations(range(N),k):
        rest=[o for o in range(N) if o not in T]
        for rho in permutations(rest):
            base=[Fr(0)]*N
            for r,o in enumerate(rho): base[o]=-B**(r+1)
            if abs(lam_max(T,base))!=d: bad+=1
            tot+=1
            if any(lam(st,T,base,False)!=0 for st in stars): cov+=1
            if any(lam(st,T,base,True)!=0 for st in stars): covc+=1
    print("N",N,"k",k,"stars",len(stars),"loc",tot,"cov_corner",cov,"cov_centered",covc,"max_bad",bad,flush=True)
