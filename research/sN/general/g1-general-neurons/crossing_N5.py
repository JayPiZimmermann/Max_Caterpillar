"""Global cancellation structure of the exact 4-neuron max_5 identity
(research/sN/dfs/h4-general-neurons/r2_spec_N5_k4.py, read only).
Lemma (proved on paper, see report): inside each braid chamber C, every neuron's argument is
linear; for each hyperplane H meeting int C, sum over neurons k with g_k|C = lam_k l_H of
d_k |lam_k| must vanish.  This script lists, per chamber, the neurons whose argument changes
sign inside C and checks the cancellation.  Exact (Fractions; sign change tested on the
chamber's extreme rays plus an LP-free criterion: a linear function changes sign in the open
cone iff it takes both signs on the rays)."""
import sys, itertools
from fractions import Fraction as Fr
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/dfs/h4-general-neurons')
import r2_spec_N5_k4 as S
N = S.N
def lin_on_chamber(lin, pairs, perm):
    # perm: coordinates from top to bottom; returns coefficient vector of g on that chamber
    pos = {v: r for r, v in enumerate(perm)}
    c = [Fr(t) for t in lin]
    for (i, j), w in pairs.items():
        if pos[i] < pos[j]:  # x_i > x_j
            c[i] += w; c[j] -= w
    return c
crossing_total = 0; ok = True; chambers_with_cross = 0
for perm in itertools.permutations(range(N)):
    # extreme rays of chamber (mod 1): r_k = indicator of top k coordinates, k=1..N-1
    rays = [[Fr(1) if perm.index(v) < k else Fr(0) for v in range(N)] for k in range(1, N)]
    cls = {}
    for idx, (d, lin, pairs) in enumerate(S.NEURONS):
        c = lin_on_chamber(lin, pairs, perm)
        vals = [sum(ci * ri for ci, ri in zip(c, r)) for r in rays]
        if any(v > 0 for v in vals) and any(v < 0 for v in vals):
            # normalise by first nonzero ray value pattern -> class key = direction of vals
            nz = next(v for v in vals if v != 0)
            key = tuple(v / abs(nz) for v in vals)
            keyn = tuple(-v for v in key)
            k = key if key in cls else (keyn if keyn in cls else key)
            lam = vals[0] if False else None
            # |lam| relative to class representative: ratio of value vectors
            rep = k
            ratio = next(v / r for v, r in zip(vals, rep) if r != 0)
            cls.setdefault(k, []).append((idx, Fr(d) * abs(ratio)))
    if cls:
        chambers_with_cross += 1
    for k, lst in cls.items():
        crossing_total += len(lst)
        if sum(v for _, v in lst) != 0:
            ok = False
print('chambers', 120, 'with sign-changing neurons', chambers_with_cross, 'neuron-chamber crossings', crossing_total, 'cancellation holds', ok)
# per neuron: number of chambers it crosses
for idx in range(len(S.NEURONS)):
    d, lin, pairs = S.NEURONS[idx]; n = 0
    for perm in itertools.permutations(range(N)):
        rays = [[Fr(1) if perm.index(v) < k else Fr(0) for v in range(N)] for k in range(1, N)]
        c = lin_on_chamber(lin, pairs, perm); vals = [sum(ci * ri for ci, ri in zip(c, r)) for r in rays]
        n += any(v > 0 for v in vals) and any(v < 0 for v in vals)
    print('neuron', idx, 'd', d, 'crosses', n, 'chambers')
