# Numerical search: exact 2-hidden-layer, bias-free ReLU nets f = sum_k d_k relu(W2 relu(A x)) for max_N on R^N.
# usage: fit.py N h1 h2 restarts seed
import sys, numpy as np
from scipy.optimize import least_squares
N,h1,h2,R,seed=map(int,sys.argv[1:6])
rng=np.random.default_rng(seed)
X=rng.standard_normal((4000,N)); X/=np.linalg.norm(X,axis=1,keepdims=True)
Y=X.max(1)
relu=lambda z:np.maximum(z,0)
def unpack(p):
    A=p[:h1*N].reshape(h1,N); W=p[h1*N:h1*N+h2*h1].reshape(h2,h1); d=p[h1*N+h2*h1:]
    return A,W,d
def res(p):
    A,W,d=unpack(p); H=relu(X@A.T); G=H@W.T; return relu(G)@d - Y
def jac(p):
    A,W,d=unpack(p); Z=X@A.T; H=relu(Z); G=H@W.T; S=relu(G); mG=(G>0)*1.0; mZ=(Z>0)*1.0
    n=len(X); J=np.zeros((n,len(p)))
    # d
    J[:,h1*N+h2*h1:]=S
    # W: df/dW_kj = d_k mG_k H_j
    J[:,h1*N:h1*N+h2*h1]=((d*mG)[:,:,None]*H[:,None,:]).reshape(n,-1)
    # A: df/dA_jl = sum_k d_k mG_k W_kj mZ_j X_l
    c=((d*mG)@W)*mZ
    J[:,:h1*N]=(c[:,:,None]*X[:,None,:]).reshape(n,-1)
    return J
best=1e9
for r in range(R):
    p=rng.standard_normal(h1*N+h2*h1+h2)
    s=least_squares(res,p,jac=jac,method='lm',max_nfev=3000)
    err=np.sqrt(np.mean(s.fun**2))
    if err<best: best=err; bp=s.x
    if err<1e-9: break
print(f"N={N} h1={h1} h2={h2} best_rms={best:.3e} restarts={r+1}")
np.save(f"fit_N{N}_{h1}_{h2}_s{seed}.npy",bp)
