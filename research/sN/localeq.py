import sys, pickle, itertools, random, numpy as np
sys.path.insert(0, 'scripts')
from vocabulary_search import relu
from scipy.optimize import milp, LinearConstraint, Bounds
N=int(sys.argv[1])
units, locs, cover = pickle.load(open(f'research/sN/data/local3_{N}.pkl','rb'))
rng=random.Random(1)
pts=[tuple(rng.randint(-50,50) for _ in range(3)) for _ in range(40)]
B=np.array([[a,b,c,relu(a-b),relu(a-c),relu(b-c)] for a,b,c in pts],float)
Q,_=np.linalg.qr(B)
def resid(v): v=np.array(v,float); return v-Q@(Q.T@v)
mx=resid([max(y) for y in pts])
def germ(key,T,order):
    h,M=key; pos={t:0 for t in T}
    for r,o in enumerate(order): pos[o]=-(r+1)
    v=list(h); inner=[]
    for (i,j) in M:
        if i in T and j in T: inner.append((i,j))
        elif pos[i]>pos[j]: v[i]+=1; v[j]-=1
    if any(v[o] for o in range(N) if o not in T): return None
    vals=[]
    for y in pts:
        yy=dict(zip(T,y))
        vals.append(relu(sum(v[t]*yy[t] for t in T)+sum(relu(yy[i]-yy[j]) for i,j in inner)))
    return resid(vals)
U=len(units)
rows=[];rhs=[]
P=np.linalg.svd(np.eye(40)-Q@Q.T)[0][:,:34]   # basis of residual space
for l,(T,o) in enumerate(locs):
    Al=np.zeros((34,U))
    for u in cover[l]:
        Al[:,u]=P.T@germ(units[u],T,o)
    rows.append(Al); rhs.append(P.T@mx)
A=np.vstack(rows); bvec=np.concatenate(rhs)
# drop dependent rows
uu,ss,vt=np.linalg.svd(np.hstack([A,bvec[:,None]]),full_matrices=False)
k=(ss>1e-8*ss[0]).sum(); A=(uu[:,:k].T@A); bvec=uu[:,:k].T@bvec; L=k
print('independent equations',k,'vars',U)
Mb=50.0
c=np.concatenate([np.zeros(U),np.ones(U)])
cons=[LinearConstraint(np.hstack([A,np.zeros((L,U))]),bvec-1e-7,bvec+1e-7),
      LinearConstraint(np.hstack([np.eye(U),-Mb*np.eye(U)]),-np.inf,0),
      LinearConstraint(np.hstack([-np.eye(U),-Mb*np.eye(U)]),-np.inf,0)]
res=milp(c,constraints=cons,integrality=np.concatenate([np.zeros(U),np.ones(U)]),
         bounds=Bounds(np.concatenate([-Mb*np.ones(U),np.zeros(U)]),np.concatenate([Mb*np.ones(U),np.ones(U)])),options={'time_limit':900})
print('min support (local equations)',res.status,res.fun, getattr(res,'mip_dual_bound',None))
