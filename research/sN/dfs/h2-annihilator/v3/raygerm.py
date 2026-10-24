"""Exact ray-germ conditions for V^TI_N inside Lambda2_N.  usage: raygerm.py N
For every ray x0 of the global fan (K_N + braid): germ map G (integer rows),
germ of V = G V.  Exact integer left-null Y of G V (flint fmpz) gives
conditions Y G vanishing on V exactly.  Ranks of the accumulated conditions on
P_N are taken mod p (lower bounds for the rational rank).
Output: per ray class: germ dims (P, V), and the rank gained over the
continuity + codim-2 conditions.  Saves conditions to raycond_N.pkl."""
import pickle, sys, time, random
from math import gcd
import flint
from core import Setup, P1, all_rays, canon, apply_rows

N = int(sys.argv[1])
t0 = time.time()
S = Setup(N)
A = S.A
p = P1
print('nvars', A.nvars, 'nV', len(S.V), f'{time.time()-t0:.0f}s', flush=True)
R = all_rays(N, S.hyps)
cls = {}
for x in R:
    cls.setdefault(canon(x), []).append(x)
print('rays', len(R), 'classes', len(cls), f'{time.time()-t0:.0f}s', flush=True)


def ray_conditions(x0):
    G = S.germ_rows(x0)
    vars_ = sorted(set().union(*[set(r) for r in G]))
    # restrict V vectors to vars
    Vs = []
    for v in S.V:
        w = {k: v[k] for k in vars_ if k in v}
        if w:
            Vs.append(w)
    GV = apply_rows(G, Vs)              # |G| x |Vs|
    # dedupe columns
    cols = sorted(set(tuple(GV[i][j] for i in range(len(G))) for j in range(len(Vs))))
    cols = [c for c in cols if any(c)]
    M = flint.fmpz_mat(len(cols), len(G), [x for c in cols for x in c]) if cols else None
    # P germ rank: rank of G on P = rank of G restricted to P (computed later); V germ rank:
    rV = M.rank() if M is not None else 0
    if M is None:
        X, nul = flint.fmpz_mat(len(G), len(G), [int(i == j) for i in range(len(G)) for j in range(len(G))]), len(G)
    else:
        X, nul = M.nullspace()
    conds = []
    for k in range(nul):
        y = [int(X[i, k]) for i in range(len(G))]
        g = 0
        for v in y:
            g = gcd(g, abs(v))
        if g == 0:
            continue
        y = [v // g for v in y]
        row = {}
        for yi, r in zip(y, G):
            if yi:
                for var, x in r.items():
                    row[var] = row.get(var, 0) + yi * x
        row = {k: x for k, x in row.items() if x}
        if row:
            conds.append(row)
    return G, conds, rV


# base: continuity + codim-2 straightness rows (reuse v2 machinery)
base = [dict(r) for r in S.C]
c2 = pickle.load(open(f'codim2_{N}.pkl', 'rb')) if len(sys.argv) < 3 else []
base += c2
print('base rows', len(base), f'{time.time()-t0:.0f}s', flush=True)
Mb = S.nmod(base, p)
rb = Mb.rank()
dimV = S.nmod(S.V, p).rank()
print('dim Lambda2 <=', A.nvars - rb, ' dim V >=', dimV, f'{time.time()-t0:.0f}s', flush=True)
acc_rows = list(base)
acc_rank = rb
out = {}
for c in sorted(cls, key=lambda c: (len(set(c)), c)):
    xs = cls[c]
    G, conds, rV = ray_conditions(xs[0])
    rP = A.nvars - S.nmod(S.C + G, p).rank()   # dim of P-germ = rank of G on P
    rP = (A.nvars - S.nmod(S.C, p).rank()) - rP
    if not conds:
        out[c] = dict(orbit=len(xs), rP=rP, rV=rV, gain=0)
        continue
    # local test: do conditions add rank to the base+acc?
    allc = []
    for x in xs:
        allc += ray_conditions(x)[1]
    M = S.nmod(acc_rows + allc, p)
    r = M.rank()
    gain = r - acc_rank
    out[c] = dict(orbit=len(xs), rP=rP, rV=rV, gain=gain, conds=allc)
    print('class', c, 'orbit', len(xs), 'germ P,V', (rP, rV), '#cond rows', len(allc), 'gain', gain, f'{time.time()-t0:.0f}s', flush=True)
    if gain:
        acc_rows += allc
        acc_rank = r
print('final: dim Lambda_rays <=', A.nvars - acc_rank, ' dim V >=', dimV)
pickle.dump(out, open(f'raycond_{N}.pkl', 'wb'))
