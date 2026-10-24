#!/usr/bin/env python3
"""L^2 closure probe WITH head-limit functions (step 14).
As heads v = v0 + lam*l -> infinity (l_apex = 0, sum l = 0, l equal on the twin pair), twin germs satisfy
g - lam relu(<l,z>) -> 1[<l,z> > 0] (<v0,z> + Phi_F(z))  in L^2_loc, and relu(<l,z>) is in W.
So the closure of span(twins, all heads) + W contains q = 1[<l,z>>0] (Phi_F - z_0) and 1[<l,z>>0] <w,z>
for real l, w in M_pair = {x_0 = 0, sum x = 0, x_a = x_b}.  We add such q for nl random real directions per
(F, twin pair) type and report the L^2 residual of SF_max (symmetrised MD transform on chamber samples).
Usage: twin_l2lim.py m npts R nl [seed]"""
import sys, itertools, time
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
import sym_md
m, npts, R, nl = map(int, sys.argv[1:5]); seed = int(sys.argv[5]) if len(sys.argv) > 5 else 3
rng = np.random.default_rng(seed)
X = np.sort(rng.dirichlet(np.ones(m), size=npts), axis=1)
cube = np.array(list(itertools.product([0, 1], repeat=m)), dtype=float)
sign = np.array([(-1) ** (m - int(s.sum())) for s in cube], dtype=float)
perms = list(itertools.permutations(range(m)))
Z = np.concatenate([(X[:, p][:, None, :] * cube[None, :, :]).reshape(-1, m) for p in perms])
def SFv(vals):
    return (vals.reshape(len(perms), npts, len(cube)) @ sign).sum(axis=0)
def Phi(F):
    s = np.zeros(len(Z))
    for i, j in F: s += np.maximum(Z[:, i] - Z[:, j], 0)
    return s
b = SFv(Z.max(axis=1))
sym_md.MODE['pred'] = sym_md.twin_leaves
fam = sym_md.family(m, R)
cols = [SFv(np.maximum(Z @ np.array(v, float) + Phi(F), 0)) for v, F in fam]
def resid(cols):
    A = np.array(cols).T
    Q, Rr = np.linalg.qr(A)
    d = np.abs(np.diag(Rr)); keep = d > 1e-10 * d.max()
    Q = Q[:, keep]; r = b - Q @ (Q.T @ b)
    return keep.sum(), np.linalg.norm(r) / np.linalg.norm(b)
print(f'm={m} npts={npts} R={R}: twins only: rank/resid', resid(cols), flush=True)
# types: (F, twin pairs) from the family (heads ignored)
def twin_pairs(v, F):
    deg = {}
    for i, j in F: deg[i] = deg.get(i, 0) + 1; deg[j] = deg.get(j, 0) + 1
    sig = {}
    for (i, j) in F:
        if deg[i] == 1: sig.setdefault((j, 'o', v[i]), []).append(i)
        if deg[j] == 1: sig.setdefault((i, 'i', v[j]), []).append(j)
    return {tuple(sorted(x[:2])) for x in sig.values() if len(x) >= 2}
types = set()
for v, F in fam:
    for pr in twin_pairs(v, F): types.add((tuple(F), pr))
print(len(types), 'types', flush=True)
for nl_now in [nl // 4, nl // 2, nl]:
    extra = []
    for F, (a, c) in sorted(types):
        PF = Phi(F) - Z[:, 0]
        # basis of M: x_0 = 0, sum = 0, x_a = x_c
        B = []
        for t in range(1, m):
            for u in range(t + 1, m):
                x = np.zeros(m); x[t] = 1; x[u] = -1; B.append(x)
        B = np.array(B); B = B[(B[:, a] == B[:, c])]
        B2 = []  # add symmetric directions e_a + e_c - 2 e_d
        for d in range(1, m):
            if d not in (a, c):
                x = np.zeros(m); x[a] = 1; x[c] = 1; x[d] = -2; B2.append(x)
        Mb = np.concatenate([B, np.array(B2)]) if len(B) else np.array(B2)
        r0 = np.random.default_rng(hash((F, a, c)) % 2**32)
        for _ in range(nl_now):
            l = r0.normal(size=len(Mb)) @ Mb
            H = (Z @ l > 0).astype(float)
            extra.append(SFv(H * PF))
            for w in Mb: extra.append(SFv(H * (Z @ w)))
    print(f'  + {len(extra)} limit functions ({nl_now} directions/type): rank/resid', resid(cols + extra), flush=True)
