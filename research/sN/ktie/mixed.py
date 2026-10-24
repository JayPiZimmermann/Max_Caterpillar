#!/usr/bin/env python3
"""k-tie localities tested by the k-th mixed difference.

Lambda_T g = sum_{S subset T} (-1)^{k-|S|} g(p_L + delta 1_S).
It kills every function that does not depend on some coordinate of T (so all
auxiliary functions when k >= 3, and all linear functions), and
Lambda_T max_N = (-1)^{k+1} delta at p_L.  For a unit with A(p_L) = 0 the germ
is g(z) = sigma(<v,z> + sum_{M(T)} sigma(z_i - z_j)), positively homogeneous,
so Lambda_T U = delta * sum_S (-1)^{k-|S|} g(1_S) (exact integers).
Units with A(p_L) != 0 are affine + hinges in T near p_L: Lambda = 0.

W_k(unit) = sum_T p_T [Lambda_T g_T != 0];  s_N >= C(N,k) / max W_k.
Usage: python3 mixed.py N k
"""
import itertools, math, sys
from fractions import Fraction
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/ktie')
sys.argv = sys.argv[:3]
import wk
N, k = wk.N, wk.k


def relu(t): return t if t > 0 else 0


def lam(v, MT):
    tot = 0
    for bits in range(1 << k):
        z = [(bits >> i) & 1 for i in range(k)]
        g = relu(sum(a * b for a, b in zip(v, z)) + sum(relu(z[i] - z[j]) for i, j in MT))
        tot += (-1) ** (k - bin(bits).count('1')) * g
    return tot


if __name__ == '__main__':
    f = math.factorial(N - k)
    best = Fraction(0); bestcfg = None; hist = {}
    for key, cfg in wk.units():
        h, M = key
        mu = [sum(1 for (i, j) in M if j == o) - h[o] for o in range(N)]
        W = Fraction(0); detail = []
        for T in itertools.combinations(range(N), k):
            Ts = set(T)
            v = [h[t] + sum(1 for (i, j) in M if i == t and j not in Ts) for t in T]
            pos = {t: n for n, t in enumerate(T)}
            MT = [(pos[i], pos[j]) for (i, j) in M if i in Ts and j in Ts]
            if lam(v, MT) == 0: continue
            cnt = wk.count_orders(Ts, M, mu)
            if not cnt: continue
            W += Fraction(cnt, f); detail.append((T, Fraction(cnt, f)))
        hist[W] = hist.get(W, 0) + 1
        if W > best: best, bestcfg = W, (key, cfg, detail)
    nloc = math.comb(N, k)
    print(f'N={N} k={k}: max W_k = {best} ({float(best):.4f}); C(N,k) = {nloc}; '
          f'bound s_N >= {nloc / best if best else "inf"} = {float(nloc / best) if best else 0:.3f}', flush=True)
    print('  argmax:', bestcfg[1] if bestcfg else None, bestcfg[2] if bestcfg else None)
