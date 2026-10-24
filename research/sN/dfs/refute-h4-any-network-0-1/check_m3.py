# Independent check of the m=3 locality characterization (a),(c),(Lambda).
# Works with the RAW network form g = l(x) + sum_{i!=j} C[i][j] s(x_i-x_j) + sum a_i s(x_i) + b_i s(-x_i) + bias,
# signed real (integer/rational) coefficients, evaluated exactly with Fractions. No normal form is used for
# the direct side.
import random, itertools
from fractions import Fraction as Fr
s=lambda y: y if y>0 else 0
def g_eval(net,x):
    N,l,C,a,b,bias=net
    v=bias+sum(l[i]*x[i] for i in range(N))
    v+=sum(C[i][j]*s(x[i]-x[j]) for i in range(N) for j in range(N) if i!=j)
    v+=sum(a[i]*s(x[i])+b[i]*s(-x[i]) for i in range(N))
    return v
def cellpt(N,T,ordO,rng):
    # random point: s > x_{o1} > ... > 0, with gaps >= 1
    hs=sorted(rng.sample(range(1,60),len(ordO)+1),reverse=True)
    x=[None]*N
    for t in T: x[t]=Fr(hs[0])+Fr(rng.randint(0,7),11)*0 # ties exact
    for o,h in zip(ordO,hs[1:]): x[o]=Fr(h)+Fr(rng.randint(1,9),20)
    return x
def lin_on_cell(net,N,T,ordO,rng):
    for _ in range(50):
        r=_lin(net,N,T,ordO,rng)
        if r is not None: return r
    raise RuntimeError('singular')
def _lin(net,N,T,ordO,rng):
    # fit affine form in (s,x_O,1) by evaluation at dim+1 random points, then verify at extra points
    k=len(ordO)+2
    import numpy  # not used for exact; use Fraction Gaussian elimination
    rows=[];rhs=[]
    pts=[cellpt(N,T,ordO,rng) for _ in range(k+5)]
    def feat(x): return [x[T[0]]]+[x[o] for o in ordO]+[Fr(1)]
    # solve with first k independent points
    A=[feat(p)+[g_eval(net,p)] for p in pts]
    # gaussian elimination least: exact solve of square system from first k rows (retry if singular)
    M=[r[:] for r in A[:k]]
    n=k
    for col in range(n):
        piv=next((r for r in range(col,n) if M[r][col]!=0),None)
        if piv is None: return None
        M[col],M[piv]=M[piv],M[col]
        for r in range(n):
            if r!=col and M[r][col]!=0:
                f=M[r][col]/M[col][col]; M[r]=[u-f*v for u,v in zip(M[r],M[col])]
    coef=[M[i][n]/M[i][i] for i in range(n)]
    for p in pts:
        assert sum(c*f for c,f in zip(coef,feat(p)))==g_eval(net,p), "not affine on cell?!"
    return coef
def formula(net,N,T,ordO):
    N,l,C,a,b,bias=net
    # normal form on orthant: C_ij s(x_i-x_j) = C_ij (max - x_j); a_i s(x_i)=a_i x_i; b_i s(-x_i)=0
    c=[[C[i][j]+C[j][i] if i!=j else 0 for j in range(N)] for i in range(N)]
    gam=[l[i]+a[i]-sum(C[j][i] for j in range(N) if j!=i) for i in range(N)]
    deg=[sum(c[i]) for i in range(N)]
    Gam=[gam[i]+deg[i] for i in range(N)]
    okA=True
    for p,o in enumerate(ordO):
        up=sum(c[o][t] for t in T)+sum(c[o][ordO[q]] for q in range(p))
        if up!=Gam[o]: okA=False
    cE=c[T[0]][T[1]]+c[T[0]][T[2]]+c[T[1]][T[2]]
    okC=(sum(Gam[t] for t in T)==cE)
    d={t:sum(c[t][u] for u in T if u!=t) for t in T}
    lam=sum(s(Gam[t])-s(d[t]-Gam[t]) for t in T)
    return okA and okC and bias==0, lam
def direct(net,N,T,ordO,rng,coef):
    zero=all(c==0 for c in coef)
    p=cellpt(N,T,ordO,rng)
    delta=Fr(1,1000)
    lam=0
    for S in range(8):
        x=p[:]
        for q in range(3):
            if S>>q&1: x[T[q]]+=delta
        sgn=(-1)**(3-bin(S).count('1'))
        lam+=sgn*s(g_eval(net,x))
    return zero, lam/delta
rng=random.Random(12345)
stats=dict(trials=0,zero=0,seen=0,mism=0)
for trial in range(4000):
    N=rng.randint(4,7); W=rng.choice([1,2,3,5])
    rv=lambda: Fr(rng.randint(-W,W),rng.choice([1,1,2,3]))
    C=[[rv() if (i!=j and rng.random()<0.6) else 0 for j in range(N)] for i in range(N)]
    l=[rv() for _ in range(N)]; a=[rv() for _ in range(N)]; b=[rv() for _ in range(N)]
    T=sorted(rng.sample(range(N),3)); O=[i for i in range(N) if i not in T]; rng.shuffle(O)
    bias=0
    net=(N,l,C,a,b,bias)
    coef=lin_on_cell(net,N,T,O,rng)
    if rng.random()<0.85:
        # subtract the affine form on the cell, spread over the T variables and O variables randomly
        l=l[:]
        # s-coefficient: distribute over T with random split
        w=[Fr(rng.randint(-3,3)) for _ in T]; w[-1]=coef[0]-sum(w[:-1])
        for t,wt in zip(T,w): l[t]-=wt
        for o,co in zip(O,coef[1:-1]): l[o]-=co
        if rng.random()<0.1:  # occasionally perturb to be nonzero
            l[rng.randrange(N)]+=Fr(1,7)
        if rng.random()<0.05: bias=Fr(1,3)
        net=(N,l,C,a,b,bias)
        coef=lin_on_cell(net,N,T,O,rng)
    zero,lamD=direct(net,N,T,O,rng,coef)
    pred,lamF=formula(net,N,T,O)
    stats['trials']+=1; stats['zero']+=zero
    if zero!=pred or (zero and lamD!=lamF):
        stats['mism']+=1; print("MISMATCH",N,T,O,zero,pred,lamD,lamF); 
    if zero and lamD!=0: stats['seen']+=1
print(stats)
