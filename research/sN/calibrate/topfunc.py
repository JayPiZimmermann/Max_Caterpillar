"""Mixed N-th difference at the origin: D f = sum_{S subset [N]} (-1)^{N-|S|} f(1_S).
D kills every function that does not depend on some coordinate near 0 in the
cube [0,1]^N sense: it kills linear functions, all auxiliary functions (N>=3)
and max_S for S != [N]; D max_N = (-1)^{N+1}.  (All functions here are
positively homogeneous, so step size 1 is no loss.)"""
import itertools, sys, collections
from core import units_of


def D_unit(N, key):
    h, M = key
    tot = 0
    for r in range(N + 1):
        for S in itertools.combinations(range(N), r):
            s = set(S)
            a = sum(h[i] for i in S) + sum(1 for i, j in M if i in s and j not in s)
            tot += (-1) ** (N - r) * max(a, 0)
    return tot


if __name__ == '__main__':
    N = int(sys.argv[1])
    U = units_of(N)
    vals = [D_unit(N, k) for k in U]
    print('N', N, 'D-value histogram', sorted(collections.Counter(vals).items()))
