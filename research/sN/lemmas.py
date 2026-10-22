#!/usr/bin/env python3
"""Test the structural lemmas behind the conjectured locality bound.

kappa_o = #hinge children + #linear children + [o = last] - [o = apex] - [parent edge linear]
L1: sum_o kappa_o = |F| (F = hinge edges).
L3: every locality passing (a) and (b') has T = {apex, u, w} with
    (A) uw in F and kappa_u + kappa_w = 2, or (B) uw not in F and {kappa_u, kappa_w} = {2, -1}.
Also reports, per unit, sum over valid T of (#orders)/(N-3)!, split by case.
"""
import itertools, math, sys
sys.argv += []
exec(open('research/sN/count_ab.py').read().split("best = 0")[0])   # reuse N, caterpillar, passes_b
bad = 0; worst = 0; worst_cfg = None
from fractions import Fraction
for size in range(1, r + 1):
    for S in itertools.combinations(range(1, r + 1), size):
        edges, last = caterpillar(S)
        for states in itertools.product(range(3), repeat=r):
            kappa = [0] * N; mu = [0] * N; nbr = [[] for _ in range(N)]
            kappa[0] -= 1; kappa[last] += 1; mu[0] += 1; mu[last] -= 1
            F = set()
            for (p, c), s in zip(edges, states):
                if s: mu[c] += 1
                if s == 1: mu[p] -= 1; kappa[p] += 1; kappa[c] -= 1
                if s == 2: kappa[p] += 1; nbr[p].append(c); nbr[c].append(p); F.add(frozenset((p, c)))
            assert sum(kappa) == len(F), 'L1'
            assert all(kappa[o] == len(nbr[o]) - mu[o] for o in range(N))
            tot = Fraction(0)
            for T in itertools.combinations(range(N), 3):
                rest = [o for o in range(N) if o not in T]
                if not passes_b(T, edges, states, last): continue
                if any(mu[o] < 0 or mu[o] > len(nbr[o]) for o in rest): continue
                idx = {o: k for k, o in enumerate(rest)}
                count = {0: 1}
                for _ in range(n_out):
                    new = {}
                    for placed, c in count.items():
                        for o in rest:
                            b = 1 << idx[o]
                            if placed & b: continue
                            below = sum(1 for u in nbr[o] if u not in T and not placed & (1 << idx[u]))
                            if below == mu[o]: new[placed | b] = new.get(placed | b, 0) + c
                    count = new
                cnt = sum(count.values())
                if not cnt: continue
                if 0 not in T: bad += 1; continue
                u, w = [t for t in T if t != 0]
                A = frozenset((u, w)) in F and kappa[u] + kappa[w] == 2
                B = frozenset((u, w)) not in F and sorted((kappa[u], kappa[w])) == [-1, 2]
                if not (A or B): bad += 1; print('L3 fails', S, states, T, kappa)
                tot += Fraction(cnt, math.factorial(n_out))
            if tot > worst: worst, worst_cfg = tot, (S, states)
print(f'N={N}: L1 ok; L3 violations {bad}; max weighted count {worst} at {worst_cfg}')
