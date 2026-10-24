r"""Numerical checks for research/sN/simplify/unified.md.

Abstract unit: forest F on n vertices (parent array), integer kappa.
Tie set T passes with order of O = V \ T iff
  (a) every o in O has exactly kappa_o neighbours above it (T above everything),
  (s) every t in T without neighbour in T has kappa_t != 0.
s = max_v #{out-leaves adjacent to v}, out-leaf = F-leaf with kappa = 1.
Quantities, at y = 1/b, b = 2 max(s,2) + 2:
  Wq = sum_T y^|T| q(T),  q = exact fraction of passing orders   (per-unit lemma: Wq <= 1)
  Wm = sum_T y^|T| 2^-nu(F[O])                                    (matching relaxation)
"""
import itertools, math, random, sys
from fractions import Fraction


def random_forest(n, rng, p=0.9):
    parent = [None] * n
    order = list(range(n)); rng.shuffle(order)
    for i, v in enumerate(order):
        if i > 0 and rng.random() < p:
            parent[v] = order[rng.randrange(i)]
    return parent


def nbrs(n, parent):
    nb = [set() for _ in range(n)]
    for v in range(n):
        if parent[v] is not None:
            nb[v].add(parent[v]); nb[parent[v]].add(v)
    return nb


def svalue(n, nb, kappa):
    out = [len(nb[u]) == 1 and kappa[u] == 1 for u in range(n)]
    return max([sum(out[u] for u in nb[v]) for v in range(n)] + [0])


def matching(nb, U):
    # maximum matching of forest induced on U (greedy leaf matching)
    U = set(U); adj = {u: set(w for w in nb[u] if w in U) for u in U}
    m = 0; alive = set(U)
    changed = True
    while changed:
        changed = False
        for u in list(alive):
            if u not in alive: continue
            deg = [w for w in adj[u] if w in alive]
            if len(deg) == 0:
                alive.discard(u); changed = True
            elif len(deg) == 1:
                w = deg[0]; alive.discard(u); alive.discard(w); m += 1; changed = True
    return m


def analyse(n, parent, kappa):
    nb = nbrs(n, parent)
    res = {}
    for mask in range(1 << n):
        Ts = {v for v in range(n) if mask >> v & 1}
        if any(not (nb[t] & Ts) and kappa[t] == 0 for t in Ts):
            continue
        O = [v for v in range(n) if v not in Ts]
        # quick necessary check
        if any(kappa[o] < 0 or kappa[o] > len(nb[o]) or len(nb[o] & Ts) > kappa[o] for o in O):
            continue
        cnt = 0
        for perm in itertools.permutations(O):
            pos = {v: i for i, v in enumerate(perm)}
            if all(sum(1 for w in nb[o] if w in Ts or pos[w] < pos[o]) == kappa[o] for o in O):
                cnt += 1
        if cnt:
            res[frozenset(Ts)] = (Fraction(cnt, math.factorial(len(O))), matching(nb, O))
    return nb, res


def weights(res, y):
    wq = sum(y ** len(T) * q for T, (q, nu) in res.items())
    wm = sum(y ** len(T) * Fraction(1, 2 ** nu) for T, (q, nu) in res.items())
    return wq, wm


def base_of(res, which):
    def W(x):
        return weights(res, Fraction(x))[which]
    lo, hi = 1e-6, 1.0
    if W(1.0) <= 1: return 1.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if W(mid) <= 1: lo = mid
        else: hi = mid
    return 1 / lo


if __name__ == "__main__":
    n, trials, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    worst = {}
    for _ in range(trials):
        parent = random_forest(n, rng)
        kappa = [rng.choice([-1, 0, 0, 1, 1, 1, 2, 2, 3]) for _ in range(n)]
        nb, res = analyse(n, parent, kappa)
        s = svalue(n, nb, kappa)
        b = 2 * max(s, 2) + 2
        wq, wm = weights(res, Fraction(1, b))
        bm = base_of(res, 1)
        key = s
        if bm > worst.get(key, (0,))[0]:
            worst[key] = (bm, float(wm), parent, kappa)
        if wm > 1:
            print("MATCHING RELAXATION > 1:", s, float(wm), parent, kappa)
    for s in sorted(worst):
        print("s=%d worst matching-base %.4f  Wm=%.4f  %s %s" % (s, *worst[s]))
