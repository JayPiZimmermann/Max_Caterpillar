"""Centre + pair-max-difference + star family, symmetric under S_{n-1} fixing the centre.
g = mu (m_P - m_Q) + sum_o s_o y_o,  y_o = sigma(x_o - x_c), s in {-1,0,1}, mu in MUS.
Conditions in the n representative chambers (identity order, centre at position p):
crossing cancellation; top = sum_k (-1)^(n-1-k) b_c(k) != 0, b_c(k)= coef of x_c when k below.
python fam_cps.py n mus(comma)"""
import sys, itertools
import numpy as np
from math import comb
from modp import rank_mod, P as PR
n = int(sys.argv[1]); MUS = [int(v) for v in sys.argv[2].split(',')]
others = list(range(1, n))
pairs = list(itertools.combinations(others, 2))
shapes = [(0, None, None)] + [(mu, Pp, Qq) for mu in MUS for Pp in pairs for Qq in pairs if Pp != Qq]
def key(mu, Pp, Qq, s):
    if mu == 0:
        return ('star', tuple(sorted(s.values())))
    sh = set(Pp) & set(Qq)
    po = tuple(sorted(s[v] for v in Pp if v not in sh)); qo = tuple(sorted(s[v] for v in Qq if v not in sh))
    sv = tuple(s[v] for v in sh)
    ne = tuple(sorted(s[v] for v in others if v not in Pp and v not in Qq))
    return (mu, po, qo, sv, ne)
types = {}; cross = {}; topcoef = {}
for p in range(n):   # centre position
    order = others[:p] + [0] + others[p:]   # element at each position (top first)
    pos = {e: i for i, e in enumerate(order)}
    for mu, Pp, Qq in shapes:
        for svals in itertools.product((-1, 0, 1), repeat=n - 1):
            s = dict(zip(others, svals))
            a = np.zeros(n, dtype=np.int64)
            if mu:
                tp = min(Pp, key=lambda v: pos[v]); tq = min(Qq, key=lambda v: pos[v])
                a[pos[tp]] += mu; a[pos[tq]] -= mu
            for o in others:
                if s[o] and pos[o] < p: a[pos[o]] += s[o]; a[p] -= s[o]
            if not a.any(): continue
            t = key(mu, Pp, Qq, s); var = types.setdefault(t, len(types))
            D = np.cumsum(a)[:-1]
            mx, mn = D.max(), D.min()
            if mx > 0 and mn >= 0:
                topcoef[var] = topcoef.get(var, 0) + (-1) ** p * comb(n - 1, p) * int(a[p])
            elif mx > 0 and mn < 0:
                g = int(np.gcd.reduce(np.abs(D))); first = int(D[np.nonzero(D)[0][0]]); sg = 1 if first > 0 else -1
                k = (p,) + tuple(int(x) for x in (sg * D) // g); lam = sg * g
                e = cross.setdefault(k, {}); e[var] = e.get(var, 0) + abs(lam)
                if lam < 0:
                    # linear part lam*key: coefficient of x_c (position p) = lam*(D_p - D_{p-1}) normalised
                    Dk = (sg * D) // g
                    dp = (Dk[p] if p < n - 1 else 0) - (Dk[p - 1] if p > 0 else 0)
                    topcoef[var] = topcoef.get(var, 0) + (-1) ** p * comb(n - 1, p) * lam * int(dp)
nv = len(types)
C = np.zeros((len(cross), nv), dtype=np.int64)
for i, e in enumerate(cross.values()):
    for v, c in e.items(): C[i, v] = c % PR
L = np.zeros((1, nv), dtype=np.int64)
for v, c in topcoef.items(): L[0, v] = c % PR
r1 = rank_mod(C); r2 = rank_mod(np.vstack([C, L]))
print('n', n, 'mus', MUS, 'types', nv, 'cross', len(cross), 'TOP', r2 > r1, flush=True)
