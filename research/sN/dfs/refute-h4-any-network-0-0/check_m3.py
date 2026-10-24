# Independent exact check of the m=3 locality characterization for signed braid second-layer neurons.
# g(x) = sum_i l_i x_i + sum_{i!=j} C[i][j] relu(x_i-x_j) + sum_i (a_i relu(x_i) + b_i relu(-x_i)) + bias
import random, itertools
from fractions import Fraction as Fr
relu=lambda v: v if v>0 else 0
def g_eval(P,x):
    l,C,a,b,bias=P; N=len(x)
    v=bias+sum(l[i]*x[i]+a[i]*relu(x[i])+b[i]*relu(-x[i]) for i in range(N))
    v+=sum(C[i][j]*relu(x[i]-x[j]) for i in range(N) for j in range(N) if i!=j)
    return v
def normal(P,N):
    l,C,a,b,bias=P
    # on orthant: relu(x_i-x_j)=max-x_j
    gam=[l[i]+a[i] for i in range(N)]; c={}
    for i in range(N):
        for j in range(N):
            if i!=j:
                e=frozenset((i,j)); c[e]=c.get(e,0)+C[i][j]; gam[j]-=C[i][j]
    return gam,c
def predicted(P,N,T,rho):
    gam,c=normal(P,N); bias=P[4]
    deg=lambda x,S: sum(c[frozenset((x,u))] for u in S if u!=x)
    Gam=[gam[i]+deg(i,range(N)) for i in range(N)]
    O=list(rho); ok=(bias==0)
    for k,o in enumerate(O):
        above=list(T)+O[:k]
        if Gam[o]!=deg(o,above): ok=False
    ET=sum(c[frozenset(e)] for e in itertools.combinations(T,2))
    if sum(Gam[t] for t in T)!=ET: ok=False
    if not ok: return 0
    return sum(relu(Gam[t])-relu(deg(t,T)-Gam[t]) for t in T)
def brute(P,N,T,rho,delta):
    # generic point in cell
    s=Fr(random.randint(1000,2000)); x=[None]*N
    for t in T: x[t]=s
    cur=s
    for o in rho:
        cur=cur-Fr(random.randint(1,300),7); x[o]=cur
    assert x[rho[-1]]>0 if rho else True
    tot=0
    for S in itertools.product([0,1],repeat=3):
        y=list(x)
        for t,e in zip(T,S): y[t]+=delta*e
        tot+=(-1)**(3-sum(S))*relu(g_eval(P,y))
    return tot/delta
def solve_vanish(P,N,T,rho):
    # adjust l so that g == 0 on the cell (restricted linear coefficients vanish)
    l,C,a,b,bias=P
    gam,c=normal(P,N)
    O=list(rho)
    for k,o in enumerate(O):
        below=O[k+1:]
        coef=gam[o]+sum(c[frozenset((o,u))] for u in below)
        l[o]-=coef
    gam,c=normal(P,N)
    scoef=sum(gam[t] for t in T)+sum(c[frozenset(e)] for e in itertools.combinations(T,2))+sum(c[frozenset((t,o))] for t in T for o in O)
    l[T[0]]-=scoef
def rnd(N,W,force_bias0):
    l=[random.randint(-W,W) for _ in range(N)]
    C=[[random.randint(-W,W) if i!=j else 0 for j in range(N)] for i in range(N)]
    a=[random.randint(-W,W) for _ in range(N)]; b=[random.randint(-W,W) for _ in range(N)]
    bias=0 if force_bias0 else random.randint(-W,W)
    return [l,C,a,b,bias]
random.seed(1)
mism=0; nz=0; cnt=0
for it in range(20000):
    N=random.randint(3,6); W=random.choice([1,2,3])
    P=rnd(N,W,random.random()<0.8)
    T=random.sample(range(N),3); O=[i for i in range(N) if i not in T]; random.shuffle(O)
    if random.random()<0.7: solve_vanish(P,N,T,O)
    delta=Fr(1,10**6)
    pr=predicted(P,N,T,O); br=brute(P,N,T,O,delta)
    cnt+=1
    if pr!=br:
        mism+=1
        if mism<5: print("MISMATCH",N,T,O,P,pr,br)
    if pr!=0: nz+=1
print("trials",cnt,"mismatches",mism,"nonzero",nz)
