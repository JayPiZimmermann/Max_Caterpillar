# Independent check (refute-logic lens): evaluate JSON nets on fresh random points, and
# a small least-squares search at excluded widths (zero biases). Seed 12345; producer: this file.
import json, sys, numpy as np
from scipy.optimize import least_squares
rng=np.random.default_rng(12345)
def ev(path):
    d=json.load(open(path)); A=np.array(d["first_layer"],float); W=np.array(d["second_layer"],float); c=np.array(d["output"],float)
    X=rng.standard_normal((200000,d["N"]))*rng.exponential(5,(200000,1))
    F=np.maximum(np.maximum(X@A.T,0)@W.T,0)@c
    return np.abs(F-X.max(1)).max()
for p in ["../net_N4_6_3.json","../net_N3_4_3.json"]: print(p,"max abs err",ev(p))
def fit(N,h1,h2,restarts):
    X=rng.standard_normal((1500,N)); X/=np.linalg.norm(X,axis=1,keepdims=True); Y=X.max(1)
    def res(p):
        A=p[:h1*N].reshape(h1,N); W=p[h1*N:h1*N+h2*h1].reshape(h2,h1); c=p[-h2:]
        return np.maximum(np.maximum(X@A.T,0)@W.T,0)@c-Y
    best=9
    for r in range(restarts):
        p0=rng.standard_normal(h1*N+h2*h1+h2)
        s=least_squares(res,p0,max_nfev=3000)
        best=min(best,np.sqrt(np.mean(s.fun**2)))
    return best
# control first: feasible widths should reach ~0
for (N,h1,h2,R) in [(3,4,3,60),(3,3,3,150),(3,3,6,100),(3,6,2,150),(4,6,3,60),(4,5,3,100),(4,5,6,60),(4,8,2,100)]:
    print(N,h1,h2,"restarts",R,"best RMS",fit(N,h1,h2,R)); sys.stdout.flush()
