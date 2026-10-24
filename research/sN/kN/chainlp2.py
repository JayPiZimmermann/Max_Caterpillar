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
from math import gcd

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
ap.add_argument('--randw', type=int, default=0)
ap.add_argument('--milp_time', type=float, default=1200)
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
    if 'shape5' in name:   # S_N-images of the neurons of known max_5 expansions (OR-basis, scaled to integers)
        import runpy, json as _j
        shapes = []
        sp = runpy.run_path('../dfs/h4-general-neurons/r2_spec_N5_k4.py')
        for d_, l, a in sp['NEURONS']:
            shapes.append((l, a))
        for nn in _j.load(open('sup5.json'))['neurons']:
            g = nn['g_or']; l = list(g[:5]); a = {}
            for k, (i, j) in enumerate(itertools.combinations(range(5), 2)):
                if g[5 + k]:
                    a[(i, j)] = g[5 + k]; l[j] += g[5 + k]   # max(x_i,x_j) = x_j + relu(x_i-x_j)
            shapes.append((l, a))
        for l, a in shapes:
            # to OR basis on 5 vars: relu(x_i-x_j) = max(x_i,x_j) - x_j
            v5 = [Fr(x) for x in l] + [Fr(0)] * 10
            p5 = list(itertools.combinations(range(5), 2))
            for (i, j), c in a.items():
                c = Fr(c); ii, jj = min(i, j), max(i, j)
                v5[5 + p5.index((ii, jj))] += c; v5[j] -= c
            den = 1
            for x in v5: den = den * x.denominator // gcd(den, x.denominator)
            v5 = [int(x * den) for x in v5]
            for img in itertools.permutations(range(N), 5):
                v = np.zeros(ORB.shape[1], np.int64)
                for i in range(5): v[img[i]] += v5[i]
                for k, (i, j) in enumerate(p5):
                    a_, b_ = sorted((img[i], img[j]))
                    v[N + pairs.index((a_, b_))] += v5[5 + k]
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


# ---- contraction of 2-member classes (union-find with ratios) ----
act = np.nonzero(alive)[0]
parent = {int(a): int(a) for a in act}
ratio = {int(a): 1.0 for a in act}          # d_a = ratio[a] * d_root
dead = set()
def find(a):
    path = []
    while parent[a] != a:
        path.append(a); a = parent[a]
    root = a
    # compress
    for x in reversed(path):
        p = parent[x]
        if p != root:
            ratio[x] *= ratio[p]
        parent[x] = root
    return root
seen = set()
multi = []
for mem, lam in rows:
    key = (tuple(int(x) for x in mem), tuple(np.round(lam, 9)))
    if key in seen: continue
    seen.add(key)
    if len(mem) == 2:
        a, b = int(mem[0]), int(mem[1]); la, lb = float(lam[0]), float(lam[1])
        ra, rb = find(a), find(b)
        # la*ratio[a]*d_ra + lb*ratio[b]*d_rb = 0
        if ra == rb:
            if abs(la * ratio[a] + lb * ratio[b]) > 1e-9: dead.add(ra)
        else:
            parent[rb] = ra
            ratio[rb] = -la * ratio[a] / (lb * ratio[b])
            if rb in dead: dead.add(ra)
    else:
        multi.append((mem, lam))
for a in act: find(int(a))
dead = {find(x) for x in dead}
changed = True
while changed:
    changed = False
    newm = []
    for mem, lam in multi:
        coef = {}
        for a, l in zip(mem, lam):
            r = find(int(a))
            if r in dead: continue
            coef[r] = coef.get(r, 0.0) + l * ratio[int(a)]
        coef = {r: c for r, c in coef.items() if abs(c) > 1e-9}
        if len(coef) == 1:
            dead.add(next(iter(coef))); changed = True
        elif coef:
            newm.append(coef)
    multi_rows = newm
groups = {}
for a in act:
    r = find(int(a))
    if r not in dead:
        groups.setdefault(r, []).append(int(a))
roots = sorted(groups)
gpos = {r: k for k, r in enumerate(roots)}
ng, nr = len(roots), ORB.shape[1]
sizes = np.array([len(groups[r]) for r in roots])
print('groups %d (sizes: max %d, mean %.2f), multi rows %d, %.0fs' % (ng, sizes.max() if ng else 0, sizes.mean() if ng else 0, len(multi_rows), time.time() - t0), flush=True)
from scipy.sparse import lil_matrix, csr_matrix, hstack, vstack
Bool = np.zeros((NS - 1, ng))
for r in roots:
    col = np.zeros(NS)
    for a in groups[r]:
        col += ratio[a] * np.maximum(G[a], 0)
    Bool[:, gpos[r]] = col[1:]
Crow = lil_matrix((len(multi_rows), ng))
for k, coef in enumerate(multi_rows):
    for r, c in coef.items():
        Crow[k, gpos[r]] = c
Aeq_d = vstack([csr_matrix(Bool), Crow.tocsr()])
Aeq_r = vstack([csr_matrix(ORB[1:].astype(float)), csr_matrix((len(multi_rows), nr))])
beq = np.concatenate([np.ones(NS - 1), np.zeros(len(multi_rows))])
# feasibility by least squares first
from scipy.sparse.linalg import lsqr
Afull = hstack([Aeq_d, Aeq_r]).tocsr()
sol = lsqr(Afull, beq, atol=1e-14, btol=1e-14, iter_lim=20000)
print('lsqr residual %.3e' % np.linalg.norm(Afull @ sol[0] - beq), flush=True)
from scipy.optimize import linprog
w = sizes.astype(float)
best = None
for itr in range(args.iters):
    A = hstack([Aeq_d, -Aeq_d, Aeq_r]).tocsr()
    c = np.concatenate([w, w, np.zeros(nr)])
    bounds = [(0, None)] * (2 * ng) + [(None, None)] * nr
    res = linprog(c, A_eq=A, b_eq=beq, bounds=bounds, method='highs')
    if res.status != 0:
        print('LP status', res.status, res.message); break
    z = res.x[:ng] - res.x[ng:2 * ng]
    supp = np.nonzero(np.abs(z) > 1e-7)[0]
    print('iter %d support groups %d neurons %d %.0fs' % (itr, len(supp), sizes[supp].sum(), time.time() - t0), flush=True)
    if best is None or sizes[supp].sum() < best[2]:
        best = (z.copy(), supp, sizes[supp].sum())
    w = sizes / (np.abs(z) + 1e-3)
if args.randw:
    union = set(best[1].tolist()) if best is not None else set()
    zmax = np.abs(best[0]).max() if best is not None else 1.0
    A = hstack([Aeq_d, -Aeq_d, Aeq_r]).tocsr()
    for k in range(args.randw):
        w = sizes * rng.uniform(0.2, 5.0, ng) ** 2
        res = linprog(np.concatenate([w, w, np.zeros(nr)]), A_eq=A, b_eq=beq, bounds=[(0, None)] * (2 * ng) + [(None, None)] * nr, method='highs')
        if res.status: continue
        z = res.x[:ng] - res.x[ng:2 * ng]
        sp_ = np.nonzero(np.abs(z) > 1e-7)[0]
        union |= set(sp_.tolist()); zmax = max(zmax, np.abs(z).max())
        print('randw %d support %d union %d' % (k, len(sp_), len(union)), flush=True)
    U = np.array(sorted(union))
    from scipy.optimize import milp, LinearConstraint, Bounds
    nu = len(U)
    Ad = Aeq_d.tocsc()[:, U]
    M = 20 * zmax
    # vars: z (nu), y (nu binary), r (nr)
    from scipy.sparse import identity
    Aeq = hstack([Ad, csr_matrix((Ad.shape[0], nu)), Aeq_r])
    I = identity(nu, format='csr')
    Aub1 = hstack([I, -M * I, csr_matrix((nu, nr))])
    Aub2 = hstack([-I, -M * I, csr_matrix((nu, nr))])
    cons = [LinearConstraint(Aeq, beq, beq), LinearConstraint(vstack([Aub1, Aub2]), -np.inf, 0)]
    c = np.concatenate([np.zeros(nu), sizes[U].astype(float), np.zeros(nr)])
    integ = np.concatenate([np.zeros(nu), np.ones(nu), np.zeros(nr)])
    lb = np.concatenate([-M * np.ones(nu), np.zeros(nu), -np.inf * np.ones(nr)])
    ub = np.concatenate([M * np.ones(nu), np.ones(nu), np.inf * np.ones(nr)])
    res = milp(c, constraints=cons, integrality=integ, bounds=Bounds(lb, ub), options={'time_limit': args.milp_time, 'disp': False})
    print('MILP status', res.status, res.message, 'objective', res.fun, flush=True)
    if res.x is not None:
        z = np.zeros(ng); z[U] = res.x[:nu]
        z[np.abs(z) < 1e-7] = 0
        supp = np.nonzero(z)[0]
        print('MILP support groups %d neurons %d' % (len(supp), sizes[supp].sum()), flush=True)
        best = (z, supp, sizes[supp].sum())
if best is not None and args.out:
    z, supp, _ = best
    neur = []
    for s_ in supp:
        r = roots[s_]
        for a in groups[r]:
            neur.append({'g_or': [int(x) for x in D[a]], 'scale': int(gg[a]), 'd_float': float(z[s_] * ratio[a])})
    json.dump({'N': N, 'neurons': neur}, open(args.out, 'w'))
    print('saved', len(neur), 'neurons to', args.out)
