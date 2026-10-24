"""Exact rank certificates for the graded H-(twisted-)invariant families.
Family: pseudo-keys (h, M) with U = relu(<h,x> + sum_M relu(x_i - x_j)); auxiliary functions are
pseudo-keys with M empty (h = e_i, -e_i, e_i - e_j for ordered i != j).  Columns = twisted orbit
sums under the Young subgroup S_mu, ordered: aux, then keys by |M|.
Lower bound: rank mod p of an integer evaluation matrix (prefix ranks = pivots in prefix).
Upper bound: every non-pivot column is lifted to a rational relation (rational reconstruction) and
verified EXACTLY on every cell of the arrangement {x_i = x_j, x_i = 0} modulo H (an H-twisted-
invariant function vanishes iff it vanishes on H-orbit representatives of cells), using float64
arithmetic only on integer data with a proven |value| < 2^53 bound (asserted).
Usage: certify.py N mu twist [extra seed]"""
import sys, json, time, itertools, math
import numpy as np
from fractions import Fraction
from common import keys, vs
from sym import act_key, young_gens, orbits, eval_keys
P = vs.P
N = int(sys.argv[1]); mu = tuple(int(c) for c in sys.argv[2]); tw = sys.argv[3]
extra = int(sys.argv[4]) if len(sys.argv) > 4 else 40; seed = int(sys.argv[5]) if len(sys.argv) > 5 else 3
t0 = time.time()
ks = keys(N)
aux = []
for i in range(N):
    e = [0] * N; e[i] = 1; aux.append((tuple(e), frozenset()))
    e = [0] * N; e[i] = -1; aux.append((tuple(e), frozenset()))
for i in range(N):
    for j in range(N):
        if i != j:
            e = [0] * N; e[i] = 1; e[j] = -1; aux.append((tuple(e), frozenset()))
aux = list(dict.fromkeys(aux))
fam = aux + ks                       # pseudo-keys; act_key works for them (M empty)
grade = [-1] * len(aux) + [len(k[1]) for k in ks]
gens = young_gens(N, mu)
orbs = [(o, odd) for o, odd in orbits(fam, act_key, gens)]
fidx = {k: n for n, k in enumerate(fam)}
cols = []
for o, odd in orbs:
    if tw == 'sgn' and odd: continue
    g = grade[fidx[next(iter(o))]]
    cols.append((g, {fidx[k]: (s if tw == 'sgn' else 1) for k, s in o.items()}))
cols.sort(key=lambda c: c[0])
grades = sorted({c[0] for c in cols})
nc = len(cols)
rng = np.random.default_rng(seed)
X = rng.integers(-10**6, 10**6, size=(nc + extra, N), endpoint=True).astype(np.int64)
EF = eval_keys(fam, X)               # (len(fam), npts)
M = np.zeros((X.shape[0], nc), dtype=np.int64)
for c, (g, co) in enumerate(cols):
    for f, s in co.items():
        M[:, c] += s * EF[f]
R, piv = vs.rref_mod_p(M)
pivset = set(piv)
t1 = time.time()
# lift kernel
rels = []
for f in range(nc):
    if f in pivset: continue
    v = {f: Fraction(1)}
    for r, pc in enumerate(piv):
        if pc > f: break
        c = int(R[r, f])
        if c: v[pc] = -vs.rational_reconstruct(c)
    den = 1
    for x in v.values(): den = math.lcm(den, x.denominator)
    rels.append((f, {c: int(x * den) for c, x in v.items()}))
# per-family-member coefficients B (len(fam) x nrel)
B = np.zeros((len(fam), len(rels)), dtype=np.float64)
for t, (f, v) in enumerate(rels):
    for c, a in v.items():
        for m, s in cols[c][1].items():
            B[m, t] += a * s
Bmax = float(np.abs(B).sum(axis=0).max()) if rels else 0.0
# cell checks
H = np.array([k[0] for k in fam], dtype=np.int64)
pairs = [(i, j) for i in range(N) for j in range(i + 1, N)]
pid = {p: n for n, p in enumerate(pairs)}
Mi = np.zeros((len(fam), len(pairs)), dtype=np.int64)
for r, k in enumerate(fam):
    for p in k[1]: Mi[r, pid[p]] = 1
D = np.zeros((len(pairs), N), dtype=np.int64)
for n, (i, j) in enumerate(pairs): D[n, i] = 1; D[n, j] = -1
# cells modulo H: H acts on labels; canonical rep = lexicographically smallest relabelled order
Hel = set([tuple(range(N))]); frontier = list(Hel)
while frontier:
    g = frontier.pop(); 
    for s in gens:
        h = tuple(s[g[i]] for i in range(N))
        if h not in Hel: Hel.add(h); frontier.append(h)
seen = set(); reps = []
for order in itertools.permutations(list(range(N)) + ['Z']):
    if order in seen: continue
    for h in Hel:
        seen.add(tuple(x if x == 'Z' else h[x] for x in order))
    reps.append(order)
bad = 0; maxabs = 0.0
for order in reps:
    pos = {v: k for k, v in enumerate(order)}
    rays = np.array(vs.cell_rays(N, order), dtype=np.int64)        # N x N
    act = [n for n, (i, j) in enumerate(pairs) if pos[i] > pos[j]]
    A = H + (Mi[:, act] @ D[act] if act else 0)
    vals = A @ rays.T
    allpos = (vals >= 0).all(axis=1); allneg = (vals <= 0).all(axis=1)
    kink = ~allpos & ~allneg
    lin = np.where(allpos[:, None], A, 0)
    g = np.gcd.reduce(np.abs(A), axis=1); g[g == 0] = 1
    d = A // g[:, None]
    first = np.array([row[np.nonzero(row)[0][0]] if row.any() else 1 for row in d])
    sgn = np.sign(first)
    d = d * sgn[:, None]; lam = g * sgn          # A = lam * d, d with positive leading entry
    lin = lin + np.where((kink & (lam < 0))[:, None], A, 0)
    coef = np.where(kink, np.abs(lam), 0)
    if not rels: continue
    L = lin.T.astype(np.float64) @ B                                 # N x nrel
    ki = np.nonzero(kink)[0]
    _, inv = np.unique(d[ki], axis=0, return_inverse=True)
    K = np.zeros((inv.max() + 1 if len(ki) else 0, len(rels)))
    np.add.at(K, inv.ravel(), coef[ki][:, None] * B[ki])
    bound = (np.abs(lin).max() + coef.max() + 1) * Bmax
    assert bound < 2 ** 52
    if np.any(L != 0) or np.any(K != 0): bad += 1
lower = [sum(1 for c in piv if cols[c][0] <= gr) for gr in grades]
upper = [sum(1 for c in cols if c[0] <= gr) - sum(1 for f, _ in rels if cols[f][0] <= gr) for gr in grades]
print(json.dumps({'N': N, 'mu': mu, 'twist': tw, 'grades': grades, 'ncols': nc, 'cell_reps': len(reps),
                  'rank_lower_prefix': lower, 'rank_upper_prefix': upper, 'failed_cells': bad,
                  'certified': bad == 0 and lower == upper, 'secs': [round(t1 - t0, 1), round(time.time() - t0, 1)]}), flush=True)
