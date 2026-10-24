"""Decode the floating-point N=5 five-neuron fit of research/sN/dfs/h4-general-neurons
(fitkp_N5_k5.npy): normalise weights, refit output coefficients, test which neurons matter."""
import numpy as np, itertools, sys
src='/home/jzimmermann/code/Max_Caterpillar/research/sN/dfs/h4-general-neurons/fitkp_N5_k5.npy'
N=5; P=list(itertools.combinations(range(N),2))
def feats(X):
    H=[np.maximum(X[:,i]-X[:,j],0) for i,j in P]
    return np.concatenate([X,np.stack(H,1)],1)
W=np.load(src).reshape(5,15)
W=W/np.abs(W).max(1,keepdims=True); W[np.abs(W)<1e-9]=0
rng=np.random.default_rng(1); X=rng.standard_normal((4000,N)); F=feats(X); y=X.max(1)
def fit(rows):
    B=np.concatenate([np.maximum(F@W[rows].T,0),F],1)
    c,*_=np.linalg.lstsq(B,y,rcond=None); return c, np.linalg.norm(B@c-y)/np.linalg.norm(y)
c,r=fit([0,1,2,3,4]); print('all5 resid',r,'d',np.round(c[:5],6))
for drop in range(5):
    rows=[i for i in range(5) if i!=drop]; print('drop',drop,fit(rows)[1])
