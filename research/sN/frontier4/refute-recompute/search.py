"""Independent counterexample search (numpy Adam + scipy LM polish), not sharing fit.py.
Model: F(x)=sum_k d_k relu(sum_j W_kj relu(a_j.x + b_j) + c_k) [+ e] ; biases optional.
Usage: search.py N h1 h2 restarts seed bias(0/1) budget_s"""
import sys, time, numpy as np
from scipy.optimize import least_squares
N,h1,h2,R,seed,bias,budget=map(int,sys.argv[1:8])
rng=np.random.default_rng(seed)
def pts(n): 
    x=rng.standard_normal((n,N)); return x/np.linalg.norm(x,axis=1,keepdims=True)
X=pts(1500); Y=X.max(1); Xv=pts(20000); Yv=Xv.max(1)
if bias:  # with biases, also test off-sphere scales
    X=X*rng.uniform(0.2,3,(len(X),1)); Y=X.max(1); Xv=Xv*rng.uniform(0.2,3,(len(Xv),1)); Yv=Xv.max(1)
sizes=[h1*N,h2*h1,h2]+([h1,h2,1] if bias else [])
def unpack(p):
    out=[];i=0
    for s in sizes: out.append(p[i:i+s]); i+=s
    A=out[0].reshape(h1,N); W=out[1].reshape(h2,h1); d=out[2]
    if bias: b,c,e=out[3],out[4],out[5][0]
    else: b=np.zeros(h1); c=np.zeros(h2); e=0.0
    return A,W,d,b,c,e
def fwd(p,X):
    A,W,d,b,c,e=unpack(p); z1=X@A.T+b; a1=np.maximum(z1,0); z2=a1@W.T+c; a2=np.maximum(z2,0)
    return a2@d+e,(A,W,d,z1,a1,z2,a2)
def jac(p,X):
    F,(A,W,d,z1,a1,z2,a2)=fwd(p,X); n=len(X)
    m2=(z2>0)*d  # n,h2
    dA1=(m2@W)*(z1>0)  # n,h1 : dF/dz1
    JA=(dA1[:,:,None]*X[:,None,:]).reshape(n,-1)
    JW=(m2[:,:,None]*a1[:,None,:]).reshape(n,-1)
    Jd=a2
    parts=[JA,JW,Jd]
    if bias: parts+= [dA1, m2, np.ones((n,1))]
    return np.hstack(parts)
P=sum(sizes); best=np.inf; t0=time.time(); r=0
while r<R and time.time()-t0<budget:
    p=rng.standard_normal(P)*rng.choice([0.5,1,1.5])
    m=np.zeros(P); v=np.zeros(P); lr=0.01
    for it in range(1500):
        idx=rng.choice(len(X),256); F,_=fwd(p,X[idx]); res=F-Y[idx]
        g=jac(p,X[idx]).T@res/len(idx)
        m=0.9*m+0.1*g; v=0.999*v+0.001*g*g; p-=lr*(m/(1-0.9**(it+1)))/(np.sqrt(v/(1-0.999**(it+1)))+1e-8)
    try:
        sol=least_squares(lambda q: fwd(q,X)[0]-Y, p, jac=lambda q: jac(q,X), method='lm', max_nfev=3000)
        p=sol.x
    except Exception as ex: pass
    err=np.abs(fwd(p,Xv)[0]-Yv).max()/np.abs(Yv).max()
    if err<best: best=err; bp=p.copy()
    r+=1
print(f"N={N} h=({h1},{h2}) bias={bias} seed={seed} restarts={r} best_val_maxrel={best:.3e} time={time.time()-t0:.0f}s",flush=True)
np.save(f"best_N{N}_{h1}_{h2}_b{bias}_s{seed}.npy",bp)
