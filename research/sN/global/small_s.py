#!/usr/bin/env python3
"""Small exact values of s_N (global/small_s.py).

N=4: test every pair of non-auxiliary normalized descriptions for an exact
     expansion (vocabulary_search.excluded_by_rank: a sampled mod-P rank that
     equals the family size certifies max_4 is NOT in the span; otherwise an
     exact expansion is searched and verified on every cell).
N=5: every expansion must hit each of the 20 triple localities (mixed third
     difference); each unit hits <= 4 of them, so a 5-unit expansion is an
     exact cover by 5 units with exactly 4 hits each.  We enumerate all such
     exact covers and test each for an exact expansion.
Usage: python3 small_s.py 4|5
"""
import itertools
import sys
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs

N = int(sys.argv[1])
K0, _ = vs.dictionary(N)
units = sorted(k for k in K0 if not vs.is_auxiliary(k))


def in_span(fam):
    if vs.excluded_by_rank(N, fam):
        return False
    return vs.exact_expansion(N, fam) is not None


if N == 4:
    found = [p for p in itertools.combinations(units, 2) if in_span(list(p))]
    singles = [u for u in units if in_span([u])]
    print(f'N=4: {len(units)} units; single-unit expansions {len(singles)}; '
          f'two-unit expansions {len(found)}')
    sys.exit()

# N = 5: triple localities with the mixed third difference
B, big = 10 ** 3, 10 ** 6
cubes = []
for T in itertools.combinations(range(N), 3):
    rest = [o for o in range(N) if o not in T]
    for order in itertools.permutations(rest):
        base = [0] * N
        for k, o in enumerate(order):
            base[o] = -B ** (k + 1) * big
        pts = []
        for sz in range(4):
            for S in itertools.combinations(T, sz):
                y = list(base)
                for t in S:
                    y[t] += 1
                pts.append((tuple(y), (-1) ** (3 - sz)))
        cubes.append(pts)
hits = {}
for u in units:
    h = frozenset(i for i, pts in enumerate(cubes) if sum(s * vs.eval_key(u, y) for y, s in pts))
    if h:
        hits[u] = h
L = len(cubes)
full = [u for u, h in hits.items() if len(h) == 4]
print(f'N=5: localities {L}; units hitting some locality {len(hits)}; with 4 hits {len(full)}')
# exact covers by 5 units of size 4 (Algorithm X, simple recursion)
covers = []
by_loc = {i: [u for u in full if i in hits[u]] for i in range(L)}


def search(covered, chosen):
    if len(covered) == L:
        covers.append(list(chosen)); return
    i = min(j for j in range(L) if j not in covered)
    for u in by_loc[i]:
        if hits[u] & covered:
            continue
        chosen.append(u)
        search(covered | hits[u], chosen)
        chosen.pop()


search(frozenset(), [])
print(f'exact covers by 5 four-hit units: {len(covers)}')
ok = [c for c in covers if in_span(c)]
print(f'covers giving an exact expansion: {len(ok)}')
for c in ok[:3]:
    print('  ', c)
