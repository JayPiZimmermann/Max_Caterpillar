# Random check: general neuron g = sum_{i!=j} w_ij relu(x_i-x_j) + sum_i (p_i relu(x_i)+q_i relu(-x_i)) + lin.
# On stratum T tied at c, outside in (0,c) ordered by rho: compare g with
# formula lin(c,x_O) + sum_{o<o'} beta |x_o-x_o'|, and germ independence of rho.
import numpy as np, itertools
rng=np.random.default_rng(0); r=lambda t:np.maximum(t,0)
N=6
for trial in range(200):
    W=rng.normal(size=(N,N)); np.fill_diagonal(W,0); p,q,l=rng.normal(size=(3,N))
    if trial%2: # zero outside-outside beta
        pass
    g=lambda x: sum(W[i,j]*r(x[i]-x[j]) for i in range(N) for j in range(N))+p@r(x)+q@r(-x)+l@x
    T=[0,1,2]; O=[3,4,5]
    B=(W+W.T)/2
    for rho in itertools.permutations(O):
        c=2.0; xO=np.sort(rng.uniform(0.1,1.9,3))[::-1]
        x=np.zeros(N); x[T]=c; x[list(rho)]=xO
        # predicted: g = L(x) + sum_{o<o'} B|..| where L = everything else evaluated linearly
        lin = sum(W[i,j]*(x[i]-x[j]) for i in T for j in O) + p@x + l@x \
              + sum((W[i,j]-W[j,i])/2*(x[i]-x[j]) for i in O for j in O if i<j)
        pred = lin + sum(B[i,j]*abs(x[i]-x[j]) for i in O for j in O if i<j)
        assert abs(pred-g(x))<1e-9
        # germ: perturb T coords by small z, compare g(x+z)-g(x) with G_T(z) (rho-free formula)
        z=rng.normal(size=3)*1e-3; y=x.copy(); y[T]+=z
        ellT=np.array([p[t]+l[t]+sum(W[t,o]-W[o,t]*0 for o in O) for t in T])  # relu(x_t-x_o) active
        G = ellT@z + sum(W[T[a],T[b]]*r(z[a]-z[b]) for a in range(3) for b in range(3) if a!=b)
        # x_T tied so g(x) contributes T-pairs 0
        assert abs((g(y)-g(x))-G)<1e-9, (g(y)-g(x),G)
print("ok")
