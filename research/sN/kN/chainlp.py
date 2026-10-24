"""Exact-structure sparse search for expansions  max_N = R + sum_k d_k relu(G_k),  G_k, R in V.

Reformulation (PROOFS.md, Section U1).  Every G in V = span{x_i, max(x_i,x_j)} is the Lovasz
extension of its set function g(S) = G(1_S), a multilinear polynomial of degree <= 2 with
g({}) = 0; translation invariance is g([N]) = 0.  For a dictionary {g_i} and real d_i the
function F = sum d_i relu(G_i) is linear on every braid cell  <=>  for every chain
C = (S_1 c ... c S_{N-1}) the neurons whose chain vector (g(S_1),...,g(S_{N-1})) takes both strict
signs group into proportionality classes with sum_i d_i |lambda_i| = 0 (lambda_i = ratio to the
class representative).  Then F is the Lovasz extension of S -> sum d_i relu(g_i(S)), and
max_N = R + F  <=>  sum_i d_i relu(g_i(S)) + r(S) = [S != {}] for all S, with r in V.
All constraints are LINEAR in (d, r).  We minimise ||d||_1 (then reweighted L1) with HiGHS.
The support found is then solved EXACTLY (fractions) and certified by cert_exact.py.

Usage: python chainlp.py N FAMILY [options]   (see families() below)
"""
import sys, itertools, time, json, argparse
import numpy as np
from fractions import Fraction as Fr

ap = argparse.ArgumentParser()
ap.add_argument('N', type=int)
ap.add_argument('family')
ap.add_argument('--maxterms', type=int, default=3)
ap.add_argument('--coefs', default='-2,-1,1,2')
ap.add_argument('--starw', default='-1,0,1')
ap.add_argument('--iters', type=int, default=6)
ap.add_argument('--out', default=None)
ap.add_argument('--seed', type=int, default=0)
ap.add_argument('--maxdict', type=int, default=3000000)
ap.add_argument('--sample', type=float, default=1.0)
args = ap.parse_args()
N = args.N
rng = np.random.default_rng(args.seed)
NS = 1 << N
bits = ((np.arange(NS)[:, None] >> np.arange(N)) & 1).astype(np.int64)
pairs = list(itertools.combinations(range(N), 2))
# OR-basis of V (translation part included): s_i and OR_ij = s_i + s_j - s_i s_j
ORB = [bits[:, i] for i in range(N)] + [bits[:, i] | bits[:, j] for i, j in pairs]
ORB = np.stack(ORB, 1).astype(np.int64)          # NS x (N + C(N,2))
names = ['s%d' % i for i in range(N)] + ['m%d%d' % p for p in pairs]
full = NS - 1


def star(b, w):
    """[b not in S] * sum_i w_i s_i  =  sum_i w_i (OR_ib - s_b)  (coefficient vector)."""
    v = np.zeros(ORB.shape[1], np.int64)
    others = [i for i in range(N) if i != b]
    for i, wi in zip(others, w):
        if wi:
            v[N + pairs.index(tuple(sorted((i, b))))] += wi
            v[b] -= wi
    return v


def families(name):
    coefs = [int(c) for c in args.coefs.split(',')]
    sw = [int(c) for c in args.starw.split(',')]
    out = []
    if 'terms' in name:   # sparse OR-basis combos with zero coefficient sum
        nb = ORB.shape[1]
        for t in range(2, args.maxterms + 1):
            for idx in itertools.combinations(range(nb), t):
                for cs in itertools.product(coefs, repeat=t):
                    if sum(cs) != 0:
                        continue
                    v = np.zeros(nb, np.int64)
                    v[list(idx)] = cs
                    out.append(v)
    if 'star' in name:
        for b in range(N):
            for w in itertools.product(sw, repeat=N - 1):
                if sum(1 for x in w if x) >= 2:
                    out.append(star(b, w))
    if 'astar' in name:   # c*(OR_P - OR_Q) + star_b(w), P,Q singles or pairs (the max_5 pattern)
        units = list(range(ORB.shape[1]))
        for p, q in itertools.permutations(units, 2):
            for c in (1, 2):
                base = np.zeros(ORB.shape[1], np.int64)
                base[p] += c; base[q] -= c
                for b in range(N):
                    for w in itertools.product(sw, repeat=N - 1):
                        if sum(1 for x in w if x) >= 2 and (args.sample >= 1 or rng.random() < args.sample):
                            out.append((base + star(b, w)).astype(np.int16))
    return out


t0 = time.time()
D = families(args.family)
D = np.unique(np.array(D), axis=0)
G = (D.astype(np.int32) @ ORB.T.astype(np.int32))                                    # dictionary set functions, ndict x NS
# keep translation-invariant (g(full)=0 holds by zero coefficient sum), genuinely sign-changing
keep = (G.max(1) > 0) & (G.min(1) < 0) & (G[:, full] == 0)
G, D = G[keep], D[keep]
# normalise by gcd and dedupe
from math import gcd
from functools import reduce
gg = np.gcd.reduce(np.abs(G), axis=1)
G = G // gg[:, None]; D = D  # D only for reporting (scaled by 1/gg)
# sigma(-g) = sigma(g) - g with g in V: keep one sign per pair (first nonzero value positive)
fnz = G[np.arange(len(G)), np.argmax(G != 0, axis=1)]
G = G * np.sign(fnz)[:, None]; D = D * np.sign(fnz)[:, None]
G, ui = np.unique(G, axis=0, return_index=True)
D, gg = D[ui], gg[ui]
if len(G) > args.maxdict:
    sel = rng.choice(len(G), args.maxdict, replace=False)
    G, D, gg = G[sel], D[sel], gg[sel]
print('dictionary', len(G), '%.0fs' % (time.time() - t0), flush=True)

# chain cut classes
perms = list(itertools.permutations(range(N)))
alive = np.ones(len(G), bool)
cls_rows = []   # list of (indices, weights)
chainsets = []
for perm in perms:
    masks = []
    m = 0
    for j in range(N - 1):
        m |= 1 << perm[j]
        masks.append(m)
    chainsets.append(masks)
V = None
def build_classes(alive):
    rows = []
    cutcount = np.zeros(len(G), np.int64)
    for masks in chainsets:
        Vc = G[:, masks]                          # ndict x (N-1)
        cut = alive & (Vc.max(1) > 0) & (Vc.min(1) < 0)
        idx = np.nonzero(cut)[0]
        if len(idx) == 0:
            continue
        W = Vc[idx]
        first = W[np.arange(len(idx)), np.argmax(W != 0, axis=1)]
        # class key: W / first (rational) -> use W * sign(first) / gcd
        sgn = np.sign(first)
        Wn = W * sgn[:, None]
        g2 = np.gcd.reduce(np.abs(Wn), axis=1)
        K = Wn // g2[:, None]
        lam = np.abs(first) / np.abs(K[np.arange(len(idx)), np.argmax(K != 0, axis=1)])
        keys, inv = np.unique(K, axis=0, return_inverse=True)
        inv = inv.ravel()
        order = np.argsort(inv, kind='stable')
        bounds_ = np.searchsorted(inv[order], np.arange(len(keys) + 1))
        for c in range(len(keys)):
            mem = order[bounds_[c]:bounds_[c + 1]]
            rows.append((idx[mem], lam[mem]))
    return rows
it = 0
while True:
    rows = build_classes(alive)
    single = [r[0][0] for r in rows if len(r[0]) == 1]
    if not single:
        break
    alive[single] = False
    it += 1
print('after %d pruning rounds alive %d, class rows %d, %.0fs' % (it, alive.sum(), len(rows), time.time() - t0), flush=True)

act = np.nonzero(alive)[0]
pos = {a: k for k, a in enumerate(act)}
nd, nr = len(act), ORB.shape[1]
# equality constraints: Boolean identity rows (NS-1) + class rows
from scipy.sparse import lil_matrix, csr_matrix, hstack, vstack
import scipy.sparse as sp
Bool = np.maximum(G[act], 0).T[1:]               # (NS-1) x nd
Rmat = ORB[1:]                                   # (NS-1) x nr
target = np.ones(NS - 1)
Crow = lil_matrix((len(rows), nd))
for k, (mem, lam) in enumerate(rows):
    for a, l in zip(mem, lam):
        Crow[k, pos[a]] = l
Aeq_d = vstack([csr_matrix(Bool.astype(float)), Crow.tocsr()])
Aeq_r = vstack([csr_matrix(Rmat.astype(float)), csr_matrix((len(rows), nr))])
beq = np.concatenate([target, np.zeros(len(rows))])
from scipy.optimize import linprog
w = np.ones(nd)
best = None
for itr in range(args.iters):
    # variables: dp (nd), dm (nd), r (nr free)
    A = hstack([Aeq_d, -Aeq_d, Aeq_r]).tocsr()
    c = np.concatenate([w, w, np.zeros(nr)])
    bounds = [(0, None)] * (2 * nd) + [(None, None)] * nr
    res = linprog(c, A_eq=A, b_eq=beq, bounds=bounds, method='highs')
    if res.status != 0:
        print('LP status', res.status, res.message); break
    d = res.x[:nd] - res.x[nd:2 * nd]
    supp = np.nonzero(np.abs(d) > 1e-7)[0]
    print('iter %d L1 %.4f support %d %.0fs' % (itr, np.abs(d).sum(), len(supp), time.time() - t0), flush=True)
    if best is None or len(supp) < len(best[1]):
        best = (d.copy(), supp)
    w = 1.0 / (np.abs(d) + 1e-3)
if best is not None and args.out:
    d, supp = best
    out = {'N': N, 'neurons': [{'g_or': [int(x) for x in D[act[s]]], 'scale': int(gg[act[s]]), 'd_float': float(d[s])} for s in supp]}
    json.dump(out, open(args.out, 'w'))
    print('saved support', len(supp), 'to', args.out)
