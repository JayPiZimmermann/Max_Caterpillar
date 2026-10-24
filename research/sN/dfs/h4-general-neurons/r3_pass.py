"""Round 3 (restart).  EXACT count of the 3-localities passed by ONE general neuron.

Neuron (translation invariant, WLOG -- see NOTE.md):
    g(x) = sum_v l_v x_v + sum_{i<j} lam_ij max(x_i, x_j),   sum l + sum lam = 0.
3-locality (T, order of O = complement, top to bottom), heights generic for the network.
Value condition (exact, generic heights): for every o in O
    c_o := l_o + sum_{j in O below o} lam_oj = 0.
Germ condition at T: passing.germ_passes (exact, Fractions).
Number of good orders of O counted by a DP over subsets (bottom-up).
Conversion to passing.py data: a_ij = lam_ij/2, kappa_v = (l_v + sum_j lam_vj)/2.
"""
import itertools
from fractions import Fraction as Fr
from functools import lru_cache
from passing import germ_passes


def lam_of(lam, i, j):
    return lam.get((min(i, j), max(i, j)), 0)


def to_ak(N, l, lam):
    a = {p: Fr(v) / 2 for p, v in lam.items() if v}
    kappa = [(Fr(l[v]) + sum(Fr(lam_of(lam, v, j)) for j in range(N) if j != v)) / 2 for v in range(N)]
    return a, kappa


def germ_ok(N, l, lam, T):
    a, kappa = to_ak(N, l, lam)
    A = lambda i, j: a.get((min(i, j), max(i, j)), 0)
    s = [2 * kappa[t] - sum(A(t, u) for u in T if u != t) for t in T]
    aT = {(0, 1): A(T[0], T[1]), (0, 2): A(T[0], T[2]), (1, 2): A(T[1], T[2])}
    return germ_passes(s, aT)


def good_orders(N, l, lam, O):
    """# orders of O (top->bottom) with c_o = 0 for all o; DP over 'set below'."""
    O = list(O)
    m = len(O)
    cnt = {0: 1}
    for size in range(m):
        new = {}
        for S, c in cnt.items():
            below = [O[i] for i in range(m) if S >> i & 1]
            for i in range(m):
                if S >> i & 1:
                    continue
                o = O[i]
                if l[o] + sum(lam_of(lam, o, j) for j in below) == 0:
                    S2 = S | (1 << i)
                    new[S2] = new.get(S2, 0) + c
        cnt = new
    return cnt.get((1 << m) - 1, 0)


def count(N, l, lam, by_T=False):
    tot = 0
    per = {}
    for T in itertools.combinations(range(N), 3):
        O = [v for v in range(N) if v not in T]
        n = good_orders(N, l, lam, O)
        if n and germ_ok(N, l, lam, T):
            tot += n
            per[T] = n
    return (tot, per) if by_T else tot


def star(N, c, w):
    """g = sum_{j != c} w_j max(x_c, x_j) + l_c x_c, l_c = -sum w (translation invariant)."""
    lam = {(min(c, j), max(c, j)): w[j] for j in range(N) if j != c and w[j]}
    l = [0] * N
    l[c] = -sum(lam.values())
    return l, lam


if __name__ == '__main__':
    import sys, math, random
    for N in range(4, 10):
        rnd = random.Random(N)
        w = [rnd.choice([1, 2, 3, -1, 5, 7]) for _ in range(N)]
        l, lam = star(N, 0, w)
        tot, per = count(N, l, lam, True)
        allL = math.comb(N, 3) * math.factorial(N - 3)
        print('N', N, 'star centre 0 w', w, 'passes', tot, 'of', allL,
              'T sets', len(per), 'of', math.comb(N, 3), 'T containing 0', math.comb(N - 1, 2), flush=True)
