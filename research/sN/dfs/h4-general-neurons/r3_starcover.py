"""Round 3.  EXACT: the signed-star family covers every 3-locality, so the locality
covering argument can never certify more than |family| = N * ceil(log2(N-1)) general
neurons.  Star(c, beta): g = sum_{j != c} eps_j (max(x_c,x_j) - x_c), eps_j = +1 if bit
beta of rank_c(j) is 1 else -1 (rank_c(j) = index of j in V \ {c}).
Checks with r3_pass.count (exact value conditions + exact germ test) that every
(T, order) is passed by some star.  Usage: python r3_starcover.py Nmax
"""
import sys, itertools, math
from r3_pass import good_orders, germ_ok


def star_signed(N, c, beta):
    others = [j for j in range(N) if j != c]
    lam, l = {}, [0] * N
    for r, j in enumerate(others):
        e = 1 if (r >> beta) & 1 else -1
        lam[(min(c, j), max(c, j))] = e
        l[c] -= e
    return l, lam


for N in range(4, int(sys.argv[1]) + 1):
    B = max(1, math.ceil(math.log2(N - 1)))
    fam = [star_signed(N, c, b) for c in range(N) for b in range(B)]
    uncovered = 0
    for T in itertools.combinations(range(N), 3):
        O = [v for v in range(N) if v not in T]
        # a star passes (T, order) for ALL orders or none (checked: good_orders == (N-3)!)
        ok = False
        for l, lam in fam:
            n = good_orders(N, l, lam, O)
            if n == math.factorial(N - 3) and germ_ok(N, l, lam, T):
                ok = True
                break
        uncovered += not ok
    print('N', N, 'stars', len(fam), 'uncovered 3-sets', uncovered, 'of', math.comb(N, 3), flush=True)
