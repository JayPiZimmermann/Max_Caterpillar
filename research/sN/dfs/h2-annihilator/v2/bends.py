"""V_N subset Lambda_N check: every bend of a unit's zero set lies on a
codim-2 flat containing >= 4 hyperplanes of Sigma_N (braid + K_N).

A bend: unit (h, M), order pi with hinge pair {p, q} adjacent (tied), zero set
of A meeting the open wall cone (gap form of g on the merged order has mixed
signs).  Flat = {x_p = x_q, g.x = 0}.  Kink hyperplanes containing it = K_N
forms a with R(a) parallel to R(g), R = (a_r, r != p, q ; a_p + a_q).
usage: bends.py N [sample]"""
import itertools, random, sys
from math import gcd
from collections import Counter
sys.path.insert(0, '..')
from ambient import units_of, primitive


def family(N):
    out = set()
    for k in range(2, N - 1):
        for T in itertools.combinations(range(N), k):
            rest = [i for i in range(N) if i not in T]
            for m in itertools.combinations_with_replacement(rest, k):
                a = [0] * N
                for t in T:
                    a[t] += 1
                for i in m:
                    a[i] -= 1
                out.add(primitive(tuple(a))[0])
    return sorted(out)


def red(a, p, q):
    v = [a[r] for r in range(len(a)) if r not in (p, q)] + [a[p] + a[q]]
    if not any(v):
        return None
    return primitive(tuple(v))[0]


if __name__ == '__main__':
    N = int(sys.argv[1])
    sample = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    K = family(N)
    pencil = {}
    for p, q in itertools.combinations(range(N), 2):
        c = Counter(red(a, p, q) for a in K)
        pencil[(p, q)] = c
    U = units_of(N)
    if sample:
        random.seed(1)
        U = random.sample(U, sample)
    stats = Counter()
    worst = None
    for (h, M) in U:
        for pi in itertools.permutations(range(N)):
            pos = {v: r for r, v in enumerate(pi)}
            for r in range(N - 1):
                a, b = pi[r], pi[r + 1]
                pr = (min(a, b), max(a, b))
                if pr not in M:
                    continue
                p, q = pr
                lo, hi = sorted([pos[p], pos[q]])
                pos2 = dict(pos)
                pos2[p], pos2[q] = lo, hi
                g = list(h)
                for (s, t) in M:
                    if (s, t) != pr and pos2[s] > pos2[t]:
                        g[s] += 1
                        g[t] -= 1
                order = [v for v in pi if v != q]
                suff, sfx = 0, []
                for v in reversed(order):
                    suff += g[v] + (g[q] if v == p else 0)
                    sfx.append(suff)
                sfx = list(reversed(sfx))[1:]
                if not (any(x > 0 for x in sfx) and any(x < 0 for x in sfx)):
                    continue
                d = g[p] - g[q]
                R = red(g, p, q)
                n = pencil[(p, q)][R]
                stats[(d, n)] += 1
    print(N, 'units', len(U), 'bends by (d, #kink lines in pencil):', sorted(stats.items()))
    print('bends with < 3 kink lines (would violate V <= Lambda):',
          sum(v for (d, n), v in stats.items() if n < 3))
