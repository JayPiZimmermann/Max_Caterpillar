"""Find N=6 unit bends at (3,1)-faces and verify the bent germ exactly."""
import itertools, sys, random
sys.path.insert(0, '..')
from bends import family, red
from collections import Counter
from germ2d import Germs, dot, rank, nullspace
N = 6
G = Germs(N)
K = family(N)
pencil = {pq: Counter(red(a, *pq) for a in K) for pq in itertools.combinations(range(N), 2)}
random.seed(3)
found = []
for (h, M) in random.sample(G.units, 400):
    for pi in itertools.permutations(range(N)):
        pos = {v: r for r, v in enumerate(pi)}
        for r in range(N - 1):
            a, b = pi[r], pi[r + 1]
            pr = (min(a, b), max(a, b))
            if pr not in M: continue
            p, q = pr
            lo, hi = sorted([pos[p], pos[q]]); pos2 = dict(pos); pos2[p], pos2[q] = lo, hi
            g = list(h)
            for (s, t) in M:
                if (s, t) != pr and pos2[s] > pos2[t]: g[s] += 1; g[t] -= 1
            order = [v for v in pi if v != q]
            suff, sfx = 0, []
            for v in reversed(order):
                suff += g[v] + (g[q] if v == p else 0); sfx.append(suff)
            sfx = list(reversed(sfx))[1:]
            if not (any(x > 0 for x in sfx) and any(x < 0 for x in sfx)): continue
            if pencil[(p, q)][red(g, p, q)] == 2:
                found.append(((h, M), pi, (p, q), g))
    if len(found) > 3: break
for (key, pi, pq, g) in found[:3]:
    print('unit', key[0], sorted(key[1]), 'order', pi, 'hinge', pq, 'g', g)
    # construct a point on the wall cone with g.x = 0: values along order merged
    p, q = pq
    order = [v for v in pi if v != q]
    # search integer heights strictly increasing along order with g.x = 0
    best = None
    for trial in range(200000):
        hts = sorted(random.sample(range(-60, 60), len(order)))
        x = [0] * N
        for v, t in zip(order, hts): x[v] = t
        x[q] = x[p]
        if dot(g, x) == 0:
            best = x; break
    x0 = best
    Hs = G.face(x0)
    print('  x0', x0, 'hyps through x0:', Hs)
    if len(Hs) != 3: continue
    Hs, u, v, rays = G.rays2d(x0)
    B = 1 + max(abs(dot(hh, r[0])) for hh in G.hyps for r in rays)
    rows = [G.germ(f, x0, rays, B) for f in G.funcs]
    print('  V germ nonlinear rank', rank(rows) - 2, '(straight would be 3, full balanced 4)')
