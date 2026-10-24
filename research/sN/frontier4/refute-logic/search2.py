# refute-logic lens, numeric complement. Seed 2026; zero biases; LM least squares on sphere points,
# validation by max abs error on 20000 fresh sphere points. Producer: this file.
import sys, time, numpy as np
from scipy.optimize import least_squares
rng=np.random.default_rng(2026)
def run(N,h1,h2,budget):
    X=rng.standard_normal((1200,N)); X/=np.linalg.norm(X,axis=1,keepdims=True); Y=X.max(1)
    V=rng.standard_normal((20000,N)); V/=np.linalg.norm(V,axis=1,keepdims=True)
    def net(p,X):
        A=p[:h1*N].reshape(h1,N); W=p[h1*N:h1*N+h2*h1].reshape(h2,h1); c=p[-h2:]
        return np.maximum(np.maximum(X@A.T,0)@W.T,0)@c
    best=9; t0=time.time(); r=0
    while time.time()-t0<budget:
        p0=rng.standard_normal(h1*N+h2*h1+h2); r+=1
        s=least_squares(lambda p: net(p,X)-Y,p0,max_nfev=2000)
        best=min(best,np.abs(net(s.x,V)-V.max(1)).max())
    print(f"N={N} h=({h1},{h2}) restarts={r} best_val_maxabs={best:.3e}",flush=True)
for cfg in [(3,4,3),(3,3,3),(3,3,8),(3,5,2),(3,8,2),(4,6,3),(4,5,3),(4,5,8),(4,10,2)]:
    run(*cfg, 60)
