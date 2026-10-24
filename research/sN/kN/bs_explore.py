"""MEASURED exploration of the braid-sign (chain-separated) neuron class.

Set-function picture: a continuous function that is linear on every braid cell is the
Lovasz extension of its values g(S) = G(1_S).  max_N <-> 1[S != {}], x_a <-> s_a,
max(x_a,x_b) <-> s_a + s_b - s_a s_b, so span Phi (translation part) <-> V = span{s_a, s_a s_b}.
If g in V never takes both strict signs along a chain {} c S_1 c ... c [N], then
relu(Lovasz g) = Lovasz(relu g) (exact).  Such neurons are 'chain-separated'.
This script samples random sparse integer g in V, keeps chain-separated ones, and tests whether
1[S != {}] lies in V + span{relu(g)} and how few neurons a greedy/L1 fit needs.
Usage: python bs_explore.py N samples W seed
"""
import sys, itertools
import numpy as np

N, M, W, seed = (int(a) for a in sys.argv[1:5])
rng = np.random.default_rng(seed)
S = np.arange(1, 1 << N)                     # nonempty subsets as bitmasks
bits = ((S[:, None] >> np.arange(N)) & 1).astype(np.int64)
mons = [(a,) for a in range(N)] + list(itertools.combinations(range(N), 2))
B = np.stack([np.prod(bits[:, list(m)], axis=1) for m in mons], 1)   # (2^N-1) x dimV
target = np.ones(len(S))

full = 1 << N
def closure_sub(ind):   # ind over all masks 0..2^N-1 ; returns OR over subsets
    a = ind.copy()
    for i in range(N):
        b = 1 << i
        idx = np.arange(full)
        sel = (idx & b) != 0
        a[sel] |= a[idx[sel] ^ b]
    return a
def closure_sup(ind):
    a = ind.copy()
    for i in range(N):
        b = 1 << i
        idx = np.arange(full)
        sel = (idx & b) == 0
        a[sel] |= a[idx[sel] | b]
    return a

def chain_sep(gv):
    pos = np.zeros(full, bool); neg = np.zeros(full, bool)
    pos[S] = gv > 0; neg[S] = gv < 0
    if not pos.any() or not neg.any():
        return False
    bad = neg & (closure_sub(pos) | closure_sup(pos))
    return not bad.any()

Q, _ = np.linalg.qr(B)
def proj(v):
    return v - Q @ (Q.T @ v)

found = {}
for t in range(M):
    k = rng.integers(2, 7)
    c = np.zeros(len(mons), np.int64)
    idx = rng.choice(len(mons), k, replace=False)
    c[idx] = rng.integers(-W, W + 1, k)
    gv = B @ c
    if chain_sep(gv):
        r = np.maximum(gv, 0)
        p = proj(r.astype(float))
        if np.linalg.norm(p) > 1e-9:
            key = tuple(np.round(p / np.abs(p).max(), 6))
            if key not in found:
                found[key] = c
print('N', N, 'distinct chain-separated relu(g) mod V:', len(found))
if found:
    A = np.stack([proj(np.maximum(B @ c, 0).astype(float)) for c in found.values()], 1)
    tp = proj(target)
    rk = np.linalg.matrix_rank(A, 1e-8)
    x, res, *_ = np.linalg.lstsq(A, tp, rcond=None)
    print('rank', rk, 'of quotient dim', len(S) - len(mons), 'target residual', np.linalg.norm(A @ x - tp))

if found and '--ann' in sys.argv:
    # annihilator of V + span relu(g) inside functions on nonempty S
    Mfull = np.concatenate([B.astype(float), np.stack([np.maximum(B @ c, 0).astype(float) for c in found.values()], 1)], 1)
    U, sv, Vt = np.linalg.svd(Mfull.T)
    r = (sv > 1e-8).sum()
    ann = Vt[r:]
    print('annihilator dim', ann.shape[0])
    for a in ann:
        a = a / a[np.argmax(np.abs(a))]
        by = {}
        for s, v in zip(S, a):
            if abs(v) > 1e-9:
                by.setdefault(round(v, 6), []).append(''.join(str(i) for i in range(N) if s >> i & 1))
        for v, l in sorted(by.items()):
            print('  %+.4f : %s' % (v, ' '.join(l)))
        print('  pairing with target', a @ target)
