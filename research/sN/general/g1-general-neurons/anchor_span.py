"""Test (cheap, small N) of the conjecture: max_N lies in V + span of anchor neurons
sigma(sum_{j!=a} c_j sigma(x_j-x_a)), c in a finite grid.  V = span{x_i, sigma(x_i-x_j)}.
Usage: python anchor_span.py N grid   (grid e.g. -1,0,1)"""
import numpy as np, itertools, sys
N=int(sys.argv[1]); grid=[int(t) for t in sys.argv[2].split(',')]
rng=np.random.default_rng(0); M=int(sys.argv[3]) if len(sys.argv)>3 else 6000
X=rng.standard_normal((M,N))
relu=lambda t: np.maximum(t,0)
cols=[X[:,i] for i in range(N)]+[relu(X[:,i]-X[:,j]) for i in range(N) for j in range(N) if i!=j]
V=np.stack(cols,1); nV=V.shape[1]
D=[]
for a in range(N):
    others=[j for j in range(N) if j!=a]
    U=np.stack([relu(X[:,j]-X[:,a]) for j in others],1)
    for c in itertools.product(grid,repeat=N-1):
        if sum(abs(t) for t in c)==0: continue
        # sign-normalise: first nonzero coefficient positive is NOT allowed (sigma not odd); keep all
        D.append(relu(U@np.array(c,float)))
D=np.stack(D,1)
B=np.concatenate([V,D],1)
y=X.max(1)
c,res,rk,sv=np.linalg.lstsq(B,y,rcond=None)
r=np.linalg.norm(B@c-y)/np.linalg.norm(y)
print('N',N,'grid',grid,'dict',D.shape[1],'rank',rk,'rel resid',r)
