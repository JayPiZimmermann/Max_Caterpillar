# Independent check of F(n) <= n-2 (Theorem CVX, m=3) with REAL weights via MILP.
# Variables: c_e >= 0 (edges), Gam_v real. Locality L=(T, order of O).
# seen(L): (a) Gam_o = up-weight, (c) sum_T Gam = c(E(T)), Lam != 0 with
# Lam = sum_t clamp(Gam_t,0,d_t) - c(E(T)). Homogeneous => normalize |Lam|>=1.
# Maximize number of seen localities W; F(n) <= n-2 iff W <= (n-2)(n-3)!.
import sys, itertools, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
n=int(sys.argv[1]); M=float(sys.argv[2]) if len(sys.argv)>2 else 100.0
V=list(range(n)); E=list(itertools.combinations(V,2)); eid={e:i for i,e in enumerate(E)}
def ce(i,j): return eid[(min(i,j),max(i,j))]
nv=0
def new(k=1):
    global nv; s=nv; nv+=k; return s
cvar=new(len(E)); gvar=new(n)
locs=[]
for T in itertools.combinations(V,3):
    O=[v for v in V if v not in T]
    for perm in itertools.permutations(O): locs.append((T,perm))
rows=[]; lo=[]; hi=[]; integ={}; lb={}; ub={}
for i in range(len(E)): lb[cvar+i]=0; ub[cvar+i]=M
for v in V: lb[gvar+v]=-n*M; ub[gvar+v]=n*M
BIG=10*n*M
def add(coefs,l,h): rows.append(coefs); lo.append(l); hi.append(h)
# clamp variables per (T,t)
clampv={}
for T in itertools.combinations(V,3):
    for t in T:
        z1=new(); w=new(); b1=new(); b2=new()
        for x in (z1,w): lb[x]=0; ub[x]=n*M
        for b in (b1,b2): lb[b]=0; ub[b]=1; integ[b]=1
        # z1 = max(G,0): z1>=G, z1>=0, z1<=G+BIG(1-b1), z1<=BIG b1
        add({z1:1,gvar+t:-1},0,np.inf)
        add({z1:1,gvar+t:-1,b1:BIG},-np.inf,BIG)
        add({z1:1,b1:-BIG},-np.inf,0)
        # d = sum c(t,s), s in T\t ; w=min(z1,d): w<=z1, w<=d, w>=z1-BIG b2, w>=d-BIG(1-b2)
        dco={cvar+ce(t,s):1 for s in T if s!=t}
        add({w:1,z1:-1},-np.inf,0)
        r={w:1}; [r.__setitem__(k,-1) for k in dco]; add(r,-np.inf,0)
        add({w:1,z1:-1,b2:BIG},0,np.inf)
        r={w:1,b2:-BIG}; [r.__setitem__(k,-1) for k in dco]; add(r,-BIG,np.inf)
        clampv[(T,t)]=w
yv=[]
for (T,perm) in locs:
    y=new(); s=new(); yv.append(y)
    for b in (y,s): lb[b]=0; ub[b]=1; integ[b]=1
    others=[]
    # (a): for o at position p (0=top), up-weight = c(o,T)+c(o, perm[:p])
    for p,o in enumerate(perm):
        r={gvar+o:1}
        for a in list(T)+list(perm[:p]): r[cvar+ce(o,a)]=r.get(cvar+ce(o,a),0)-1
        r1=dict(r); r1[y]=BIG; add(r1,-np.inf,BIG)
        r2=dict(r); r2[y]=-BIG; add(r2,-BIG,np.inf)
    r={gvar+t:1 for t in T}
    for e in itertools.combinations(T,2): r[cvar+ce(*e)]=-1
    r1=dict(r); r1[y]=BIG; add(r1,-np.inf,BIG)
    r2=dict(r); r2[y]=-BIG; add(r2,-BIG,np.inf)
    # Lam = sum w - c(E(T)); if y: Lam>=1 (s=0) or Lam<=-1 (s=1)
    L={clampv[(T,t)]:1 for t in T}
    for e in itertools.combinations(T,2): L[cvar+ce(*e)]=-1
    r1=dict(L); r1[y]=-BIG; r1[s]=BIG; add(r1,1-BIG,np.inf)
    r2=dict(L); r2[y]=BIG; r2[s]=BIG; add(r2,-np.inf,-1+2*BIG)
A=np.zeros((len(rows),nv))
for i,r in enumerate(rows):
    for k,v in r.items(): A[i,k]+=v
cobj=np.zeros(nv); cobj[yv]=-1
integrality=np.array([integ.get(i,0) for i in range(nv)])
bl=np.array([lb.get(i,-np.inf) for i in range(nv)]); bu=np.array([ub.get(i,np.inf) for i in range(nv)])
res=milp(cobj,constraints=LinearConstraint(A,lo,hi),integrality=integrality,bounds=Bounds(bl,bu),options={"time_limit":3000,"disp":False})
print("n",n,"M",M,"status",res.status,res.message)
x=res.x; W=round(-res.fun); import math
print("max W =",W," f =",W/math.factorial(n-3)," claim bound (n-2) =",n-2, " dual bound", getattr(res,'mip_dual_bound',None))
print("c:",{E[i]:round(x[cvar+i],4) for i in range(len(E)) if abs(x[cvar+i])>1e-7})
print("Gam:",[round(x[gvar+v],4) for v in V])
print("seen:",[locs[i] for i,y in enumerate(yv) if x[y]>0.5])
np.save(sys.argv[3] if len(sys.argv)>3 else "/dev/null", x[:cvar+len(E)+n]) if len(sys.argv)>3 else None
