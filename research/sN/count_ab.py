#!/usr/bin/env python3
"""Count, for every caterpillar face unit, the localities passing condition (a).

A locality is L = (T, order): |T| = 3, the coordinates in T tie at the top and
the other N-3 coordinates lie strictly below in the given order. For a unit
U_{h,M} the test functional at L can be nonzero only if, for every o outside T,

    #{hinge neighbours of o that lie below o}  =  mu_o  :=  |N^-(o)| - h_o,

where N^-(o) are the hinge neighbours with smaller index (normalized key).
mu_o does not depend on the normalization; on the caterpillar tree it equals
[o = apex] - [o = last] + [parent edge of o is linear or hinge]
    - #{children of o joined by a linear edge}.
This script enumerates caterpillars with the identity labelling (the count is
invariant under relabelling) and reports the maximum, over units, of the number
of localities passing (a), divided by (N-3)!.

Usage: python3 research/sN/count_a.py N
"""
import itertools
import math
import sys

N = int(sys.argv[1])
MODE = sys.argv[2] if len(sys.argv) > 2 else 'a'


def passes_b(T, edges, states, last):
    """(b'): a hinge edge inside T, or the T-part of the outer slope is not a root multiple.

    On the stratum, the outer argument restricted to the T coordinates is
    v_T = (e_last - e_apex)|_T + sum of linear edges inside T + hinge edges from T
    to outside that are active (T lies above), all restricted to T.
    """
    Ts = set(T)
    v = {t: 0 for t in T}
    def add(a, b, c=1):   # add c*(e_a - e_b) restricted to T
        if a in Ts: v[a] += c
        if b in Ts: v[b] -= c
    add(last, 0)
    for (p, c), s in zip(edges, states):
        if s == 2 and p in Ts and c in Ts:
            return True
        if s == 1:
            add(p, c)
        if s == 2 and (p in Ts) != (c in Ts):
            # active iff the T endpoint is the parent (e_p - e_c > 0 when p is above)
            if p in Ts:
                add(p, c)
    vals = sorted(v.values())
    nz = [x for x in vals if x]
    if not nz:
        return False
    if len(nz) == 2 and nz[0] == -nz[1]:
        return False   # multiple of a root e_a - e_b
    return True
r = N - 2
n_out = N - 3


def caterpillar(S):
    """Tree on positions 1..r+1 (labels = positions), apex 0, last spine vertex."""
    edges = []
    for j in range(1, r + 1):
        p = max([0] + [i for i in S if i < j])
        edges.append((p + 1, j + 1))          # (parent, child)
    return edges, max(S) + 1


best = 0
best_cfg = None
hist = {}
for size in range(1, r + 1):
    for S in itertools.combinations(range(1, r + 1), size):
        edges, last = caterpillar(S)
        for states in itertools.product(range(3), repeat=r):   # 0 omit, 1 lin, 2 hinge
            mu = [0] * N
            mu[0] += 1
            mu[last] -= 1
            nbr = [[] for _ in range(N)]
            for (p, c), s in zip(edges, states):
                if s:
                    mu[c] += 1
                if s == 1:
                    mu[p] -= 1
                if s == 2:
                    nbr[p].append(c)
                    nbr[c].append(p)
            total = 0
            for T in itertools.combinations(range(N), 3):
                rest = [o for o in range(N) if o not in T]
                if MODE == 'b' and not passes_b(T, edges, states, last):
                    continue
                if any(mu[o] < 0 or mu[o] > len(nbr[o]) for o in rest):
                    continue
                idx = {o: k for k, o in enumerate(rest)}
                # DP over the set of outside vertices already placed (from the top)
                count = {0: 1}
                for _ in range(n_out):
                    new = {}
                    for placed, c in count.items():
                        for o in rest:
                            b = 1 << idx[o]
                            if placed & b:
                                continue
                            # neighbours of o below o = hinge nbrs outside T not yet placed
                            below = sum(1 for u in nbr[o] if u not in T and not placed & (1 << idx[u]))
                            if below == mu[o]:
                                new[placed | b] = new.get(placed | b, 0) + c
                    count = new
                total += sum(count.values())
            hist[total] = hist.get(total, 0) + 1
            if total > best:
                best, best_cfg = total, (S, states)

f = math.factorial(n_out)
print(f'N={N}: max localities passing (a) per unit = {best} = {best / f:.3f} (N-3)!;',
      f'localities = {math.factorial(N) // 6}; bound s_N >= {math.factorial(N) / 6 / best:.3f}')
print('best config S, states:', best_cfg)
print('histogram (count: units):', dict(sorted(hist.items())))
