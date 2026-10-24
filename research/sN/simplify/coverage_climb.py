"""Hill-climb for instances with large base c (smallest c with sum_T c^-|T| q(T) <= 1), per s.
Usage: python3 coverage_climb.py n steps seed"""
import random, sys
from fractions import Fraction
from coverage_check import analyse, best_base, random_forest, W

n, steps, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
best = {}
for restart in range(6):
    parent = random_forest(n, rng)
    kappa = [rng.choice([0, 1, 1, 2]) for _ in range(n)]
    s, res = analyse(n, parent, kappa); cur = best_base(res)
    for _ in range(steps):
        p2, k2 = parent[:], kappa[:]
        if rng.random() < 0.5:
            k2[rng.randrange(n)] = rng.choice([-1, 0, 1, 2, 3])
        else:
            v = rng.randrange(n)
            # reattach v to a vertex not in its subtree, or make root
            sub = {v}; changed = True
            while changed:
                changed = False
                for u in range(n):
                    if u not in sub and p2[u] in sub:
                        sub.add(u); changed = True
            cand = [u for u in range(n) if u not in sub] + [None]
            p2[v] = rng.choice(cand)
        s2, r2 = analyse(n, p2, k2)
        assert W(r2, Fraction(3, 16 * (s2 + 1))) <= 1
        c2 = best_base(r2)
        if c2 >= cur or rng.random() < 0.05:
            parent, kappa, s, cur = p2, k2, s2, c2
        if c2 > best.get(s2, (0,))[0]:
            best[s2] = (c2, p2, k2)
for s in sorted(best):
    print("s=%d best base %.4f parent=%s kappa=%s" % (s, *best[s]))
