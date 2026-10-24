"""k-center role families.  g = sum_{center pairs} C_ij sigma(x_zi - x_zj) + sum_o sum_j
 [r_out_j sigma(x_o - x_zj) + r_in_j sigma(x_zj - x_o)].   Usage: python fam_centers.py N famname"""
import sys, itertools
from collections import Counter
from symtop import analyze, hinge
N = int(sys.argv[1]); fam = sys.argv[2]

def run(k, center_opts, roles):
    neurons = Counter()
    for zpos in itertools.permutations(range(N), k):
        gen = [p for p in range(N) if p not in zpos]
        for ci, copt in enumerate(center_opts):
            base = [0] * N
            for (i, j), w in copt.items(): hinge(N, base, zpos[i], zpos[j], w)
            for ra in itertools.product(range(len(roles)), repeat=len(gen)):
                a = list(base)
                for o, ri in zip(gen, ra):
                    out, inn = roles[ri]
                    for j in range(k):
                        if out[j]: hinge(N, a, o, zpos[j], out[j])
                        if inn[j]: hinge(N, a, zpos[j], o, inn[j])
                t = (ci, tuple(sorted(Counter(ra).items())))
                neurons[(t, tuple(a))] += 1
    return analyze(N, [(t, list(a), m) for (t, a), m in neurons.items()], want_exact=True)

if fam == 'dstar':   # double star: x_a - x_c + sum_P sigma(x_o-x_a) - sum_M sigma(x_o - x_c)
    co = [{(0, 1): 1, (1, 0): -1}, {}]
    roles = [((0, 0), (0, 0)), ((1, 0), (0, 0)), ((0, -1), (0, 0)), ((-1, 0), (0, 0)), ((0, 1), (0, 0))]
    r = run(2, co, roles)
elif fam == 'dstar2':  # all out-roles in {-1,0,1}^2
    co = [{(0, 1): 1, (1, 0): -1}, {}, {(0, 1): 1}, {(0, 1): -1}]
    roles = [((u, v), (0, 0)) for u in (-1, 0, 1) for v in (-1, 0, 1)]
    r = run(2, co, roles)
elif fam == 'star2':  # one center, in and out roles
    co = [{}]
    roles = [((u,), (v,)) for u in (-1, 0, 1) for v in (-1, 0, 1)]
    r = run(1, co, roles)
if r['top']:
    for v, val in sorted(r['sol'].items()):
        if val: print('  ', r['typenames'][v], val)
