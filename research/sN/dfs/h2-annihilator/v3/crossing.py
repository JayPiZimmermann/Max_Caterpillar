"""Compare per-cell unit kink sets D_pi with ALL kink-family hyperplanes
crossing the open braid cell pi.  usage: crossing.py N"""
import itertools, sys
sys.path.insert(0, '..'); sys.path.insert(0, '../v2')
from ambient import unit_kink_sets, units_of, primitive
from bends import family

def x_to_gap(a, pi):
    # a.x on cell pi in gap coords: x_pi(j) = x_pi(0) + t_1..t_j ; a.1 = 0
    N = len(pi)
    return tuple(sum(a[pi[r]] for r in range(j, N)) for j in range(1, N))

N = int(sys.argv[1])
U = units_of(N)
perms, data, D = unit_kink_sets(N, U)
K = family(N)
tot_all = tot_D = 0
missing = 0
for pi, ds in zip(perms, D):
    cross = set()
    for a in K:
        g = x_to_gap(a, pi)
        if any(v > 0 for v in g) and any(v < 0 for v in g):
            cross.add(primitive(g)[0])
    assert set(ds) <= cross
    tot_all += len(cross); tot_D += len(ds)
    missing += len(cross - set(ds))
print(N, 'family', len(K), 'avg crossing/cell', tot_all/len(perms), 'avg unit kinks/cell', tot_D/len(perms), 'missing total', missing)
