"""Is D_pi (unit kink dirs on cell pi) = all forms of the family
K_N = {sum_T e_t - sum m_i e_i : |T| = |m| in 2..N-2, supp disjoint} crossing the cell?"""
import itertools, sys
from collections import Counter
from ambient import unit_kink_sets, units_of, primitive, gap_form
from hyperplanes import global_hyperplanes

def family(N):
    out = set()
    for k in range(2, N - 1):
        for T in itertools.combinations(range(N), k):
            rest = [i for i in range(N) if i not in T]
            for m in itertools.combinations_with_replacement(rest, k):
                a = [0] * N
                for t in T: a[t] += 1
                for i in m: a[i] -= 1
                if any(a[i] > 0 for i in m): continue
                out.add(primitive(tuple(a))[0])
    return out

N = int(sys.argv[1])
H, B = global_hyperplanes(N)
F = family(N)
print('family', len(F), 'global kink', len(H), 'equal', F == set(H))
perms, data, D = unit_kink_sets(N, units_of(N))
bad = 0
for pi, ds in zip(perms, D):
    cross = set()
    for a in F:
        g = gap_form(a, pi)
        if any(v > 0 for v in g) and any(v < 0 for v in g):
            cross.add(primitive(g)[0])
    if cross != set(ds):
        bad += 1
print('cells where D_pi != crossing family:', bad)
