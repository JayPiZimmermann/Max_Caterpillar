r"""Exact check of the out-leaf coverage bound (research/sN/simplify/coverage.md).

Abstract setting: a forest F on n vertices (hinge forest), integer kappa arbitrary.
A tie set T passes with an order rho of O = V \ T iff
  (a) every o in O has exactly kappa_o neighbours above it (T is above everything),
  (s) every t in T without a neighbour in T has kappa_t != 0.
q(T) = #{orders of O satisfying (a)} / |O|!.
s = max over vertices v of #{out-leaves adjacent to v}; out-leaf = F-leaf with kappa = 1.
Claim: sum_T x^|T| q(T) <= 1 for x = 3/(16(s+1)).
Also checks the lemmas L1 (T determined by T cap H), L2 (|H \ T| <= (s+1)(|T|+|Y'|)),
and reports the smallest base c (= 1/x) that works for each instance.
Usage: python3 coverage_check.py n trials seed
"""
import itertools, math, random, sys
from fractions import Fraction


def random_forest(n, rng):
    parent = [None] * n
    order = list(range(n))
    rng.shuffle(order)
    for i, v in enumerate(order):
        if i > 0 and rng.random() < 0.85:
            parent[v] = order[rng.randrange(i)]
    return parent


def analyse(n, parent, kappa):
    nbr = [set() for _ in range(n)]
    for v in range(n):
        if parent[v] is not None:
            nbr[v].add(parent[v]); nbr[parent[v]].add(v)
    children = [[c for c in range(n) if parent[c] == v] for v in range(n)]
    outleaf = [len(nbr[u]) == 1 and kappa[u] == 1 for u in range(n)]
    s = max(sum(outleaf[u] for u in nbr[v]) for v in range(n))
    H = [v for v in range(n) if kappa[v] >= 1]
    res = {}  # T -> q
    for mask in range(1 << n):
        T = [v for v in range(n) if mask >> v & 1]
        Ts = set(T)
        if any(not (nbr[t] & Ts) and kappa[t] == 0 for t in T):
            continue
        O = [v for v in range(n) if v not in Ts]
        cnt = 0
        for perm in itertools.permutations(O):
            pos = {v: i for i, v in enumerate(perm)}
            ok = True
            for o in O:
                up = sum(1 for w in nbr[o] if w in Ts or pos[w] < pos[o])
                if up != kappa[o]:
                    ok = False; break
            if ok:
                cnt += 1
        if cnt:
            res[frozenset(T)] = Fraction(cnt, math.factorial(len(O)))
    # L1: T determined by T cap H
    seen = {}
    for T in res:
        X = frozenset(T & set(H))
        assert X not in seen, ("L1 fails", parent, kappa, T, seen[X])
        seen[X] = T
    # L2
    for T in res:
        Ys = [y for y in range(n) if y not in T and any(c not in T for c in children[y])]
        HO = [u for u in H if u not in T]
        assert len(HO) <= (s + 1) * (len(T) + len(Ys)), ("L2 fails", parent, kappa, T)
    return s, res


def W(res, x):
    return sum(x ** len(T) * q for T, q in res.items())


def best_base(res):
    lo, hi = 1e-9, 1.0
    if W(res, 1.0) <= 1:
        return 1.0
    for _ in range(60):
        mid = (lo + hi) / 2
        if W(res, mid) <= 1:
            lo = mid
        else:
            hi = mid
    return 1 / lo


def main():
    n, trials, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    worst = {}
    for _ in range(trials):
        parent = random_forest(n, rng)
        kappa = [rng.choice([-1, 0, 0, 1, 1, 1, 2, 2, 3]) for _ in range(n)]
        s, res = analyse(n, parent, kappa)
        x = Fraction(3, 16 * (s + 1))
        w = W(res, x)
        assert w <= 1, ("BOUND FAILS", parent, kappa, s, float(w))
        c = best_base(res)
        if c > worst.get(s, (0,))[0]:
            worst[s] = (c, parent, kappa)
    for s in sorted(worst):
        print("s=%d worst base %.4f (proved %.4f)  example parent=%s kappa=%s"
              % (s, worst[s][0], 16 * (s + 1) / 3, worst[s][1], worst[s][2]))


if __name__ == "__main__":
    main()
