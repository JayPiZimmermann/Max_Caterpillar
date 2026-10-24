"""EXACT: for an expansion max_N = R + sum d_k relu(G_k) (spec in r2_certify.py format), list, for every
braid chain (permutation, top first), the neurons whose linear form changes sign inside the cell,
grouped by proportional chain vectors (g_k(S_1..S_N), S_j = top-j set).  Shows how the bending
cancels.   Usage: python3 cut_pattern.py spec.py
"""
import sys, runpy, itertools
from fractions import Fraction as Fr
from collections import defaultdict
spec = runpy.run_path(sys.argv[1])
N, NEU = spec['N'], spec['NEURONS']

def gval(l, a, S):
    # g(1_S) = sum l_i [i in S] + sum a_ij relu([i in S]-[j in S])
    return sum(Fr(l[i]) for i in S) + sum(Fr(c) for (i, j), c in a.items() if i in S and j not in S)

stats = defaultdict(int)
for perm in itertools.permutations(range(N)):
    vecs = []
    for k, (d, l, a) in enumerate(NEU):
        v = [gval(l, a, set(perm[:j])) for j in range(1, N + 1)]
        if any(x > 0 for x in v) and any(x < 0 for x in v):
            vecs.append((k, Fr(d), v))
    groups = []
    for k, d, v in vecs:
        piv = next(x for x in v if x != 0)
        key = tuple(x / abs(piv) * (1 if piv > 0 else 1) for x in v)
        for gp in groups:
            # proportional?
            w = gp[0][2]
            ratio = None; ok = True
            for x, y in zip(v, w):
                if y == 0 and x != 0 or x == 0 and y != 0: ok = False; break
                if y != 0:
                    r = x / y
                    if ratio is None: ratio = r
                    elif r != ratio: ok = False; break
            if ok:
                gp.append((k, d, v, ratio)); break
        else:
            groups.append([(k, d, v, Fr(1))])
    sig = tuple(sorted(tuple(sorted(x[0] for x in gp)) for gp in groups))
    stats[sig] += 1
    for gp in groups:
        assert sum(x[1] * abs(x[3]) for x in gp) == 0, (perm, gp)
for s, c in sorted(stats.items(), key=lambda t: -t[1]):
    print(c, 'chains: cut groups', s)
print('all groups cancel')
