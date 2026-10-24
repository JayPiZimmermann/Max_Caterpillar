"""EXACT count of the 3-localities seen by one general second-layer neuron (positive orthant).

Neuron g = sum_v gam_v x_v + sum_{u<v} c_uv max(x_u, x_v)  (real/rational weights).
Locality (T, rho): T (3-set) tied on top, O = V\\T strictly ordered below.
Seen iff (a) every o in O has down-weight c(o, below_O(o)) = -gam_o,
(c) sum_T gam_t + c(T,O) + c(E(T)) = 0, (L) sum_t relu(Gam_t) - relu(d_t - Gam_t) != 0,
Gam_t = gam_t + deg(t), d_t = c(t, T\\t).   (research/sN/dfs/h4-any-network/r3/NOTE.md)
f = (#seen localities)/(n-3)!.  Bottom-up peeling (P1): with gamX_o = gam_o + c(o, V\\X),
f(X) = (1/(|X|-3)) * sum_{b in X, gamX_b = 0} f(X - b), f(T) = [(c) and (L)].
All arithmetic exact (Fractions) when weights are Fractions/ints.
"""
from fractions import Fraction as Fr
from functools import lru_cache
import itertools


def make_f(n, c, gam):
    """c: dict {(u,v): w} u<v ; gam: list. Returns f(full set) as Fraction."""
    W = [[0] * n for _ in range(n)]
    for (u, v), w in c.items():
        W[u][v] = W[v][u] = w
    deg = [sum(W[v]) for v in range(n)]
    full = (1 << n) - 1

    def gamX(X, o):
        return gam[o] + sum(W[o][u] for u in range(n) if not (X >> u) & 1)

    @lru_cache(maxsize=None)
    def f(X):
        m = bin(X).count('1')
        if m == 3:
            T = [v for v in range(n) if X >> v & 1]
            gT = [gamX(X, t) for t in T]  # gam_t + c(t,O)
            eT = W[T[0]][T[1]] + W[T[0]][T[2]] + W[T[1]][T[2]]
            if sum(gT) + eT != 0:
                return Fr(0)
            lam = 0
            for i, t in enumerate(T):
                d = sum(W[t][s] for s in T if s != t)
                G = gT[i] + d          # Gam_t
                lam += max(G, 0) - max(d - G, 0)
            return Fr(1) if lam != 0 else Fr(0)
        tot = Fr(0)
        for b in range(n):
            if X >> b & 1 and gamX(X, b) == 0:
                tot += f(X & ~(1 << b))
        return tot / (m - 3)

    return f(full)


def brute(n, c, gam):
    """Independent check: enumerate all (T, order of O) and test (a),(c),(L) directly."""
    W = [[0] * n for _ in range(n)]
    for (u, v), w in c.items():
        W[u][v] = W[v][u] = w
    cnt = 0
    for T in itertools.combinations(range(n), 3):
        O = [v for v in range(n) if v not in T]
        cT = sum(gam[t] for t in T) + sum(W[t][o] for t in T for o in O) + W[T[0]][T[1]] + W[T[0]][T[2]] + W[T[1]][T[2]]
        if cT != 0:
            continue
        lam = 0
        for t in T:
            d = sum(W[t][s] for s in T if s != t)
            G = gam[t] + sum(W[t])
            lam += max(G, 0) - max(d - G, 0)
        if lam == 0:
            continue
        for perm in itertools.permutations(O):   # perm[0] = bottom
            if all(sum(W[perm[i]][perm[j]] for j in range(i)) == -gam[perm[i]] for i in range(len(perm))):
                cnt += 1
    import math
    return Fr(cnt, math.factorial(n - 3))


if __name__ == '__main__':
    import random
    rnd = random.Random(1)
    for trial in range(300):
        n = rnd.randint(4, 7)
        c = {}
        for e in itertools.combinations(range(n), 2):
            if rnd.random() < 0.5:
                c[e] = rnd.choice([-2, -1, 1, 2])
        gam = [rnd.choice([0, 0, 0, -1, 1, -2, 2]) for _ in range(n)]
        # make translation-compatible sometimes
        a, b = make_f(n, c, gam), brute(n, c, gam)
        assert a == b, (n, c, gam, a, b)
    # signed star check: f = |P||Q|
    for n in range(5, 10):
        P = list(range(1, 1 + (n - 1) // 2)); Q = list(range(1 + (n - 1) // 2, n))
        c = {(0, p): 1 for p in P}; c.update({(0, q): -1 for q in Q})
        gam = [-len(P) + len(Q)] + [0] * (n - 1)
        print('star n', n, 'f', make_f(n, c, gam), 'expected', len(P) * len(Q))
    print('peeling == brute on 300 random instances')
