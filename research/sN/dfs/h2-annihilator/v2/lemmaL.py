"""Lemma (L): no unit bends at a (3,1)-face.

For a unit (h, M) and an order pi of the coordinates in which i, j are
adjacent (tied on the wall x_i = x_j) and the pair {i, j} is a hinge of M,
let g be the gradient of A on the side where the hinge is inactive, and
d = g_p - g_q where sigma(x_p - x_q) is the hinge (active iff x_p > x_q).
The zero set of A bends from g to its mirror s_pq g iff d = -1.
Report all (unit, pi, hinge) with d = -1 and whether the zero set of A meets
the relative interior of the wall cone (gap form of g on the wall has mixed
signs or g vanishes on the wall).  usage: lemmaL.py N [sample]"""
import itertools, random, sys
sys.path.insert(0, '..')
from ambient import units_of

N = int(sys.argv[1])
sample = int(sys.argv[2]) if len(sys.argv) > 2 else 0
U = units_of(N)
if sample:
    random.seed(1)
    U = random.sample(U, sample)
cnt = {'checked': 0, 'd=-1': 0, 'd=-1 & crossing': 0}
from collections import Counter
dist = Counter()
for (h, M) in U:
    for pi in itertools.permutations(range(N)):
        pos = {v: r for r, v in enumerate(pi)}
        for r in range(N - 1):
            a, b = pi[r], pi[r + 1]
            pr = (min(a, b), max(a, b))
            if pr not in M:
                continue
            p, q = pr                     # hinge sigma(x_p - x_q)
            # side where hinge inactive: x_p < x_q.  positions: treat the tied
            # pair as p below q.
            pos2 = dict(pos)
            lo, hi = sorted([pos[p], pos[q]])
            pos2[p], pos2[q] = lo, hi
            g = list(h)
            for (s, t) in M:
                if (s, t) == pr:
                    continue
                if pos2[s] > pos2[t]:
                    g[s] += 1
                    g[t] -= 1
            d = g[p] - g[q]
            cnt['checked'] += 1
            dist[d] += 1
            if d != -1:
                continue
            cnt['d=-1'] += 1
            # wall cone: order pi with p, q merged; gap form of g
            order = [v for v in pi if v != q]
            vals = []
            suff = 0
            sfx = []
            for v in reversed(order):
                suff += g[v] + (g[q] if v == p else 0)
                sfx.append(suff)
            sfx = list(reversed(sfx))[1:]
            if (any(x > 0 for x in sfx) and any(x < 0 for x in sfx)) or not any(sfx):
                cnt['d=-1 & crossing'] += 1
                if cnt['d=-1 & crossing'] <= 5:
                    print('  example', h, sorted(M), pi, (p, q), g)
print(N, 'units', len(U), cnt, 'd distribution', sorted(dist.items()))
