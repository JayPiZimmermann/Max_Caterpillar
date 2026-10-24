#!/usr/bin/env python3
"""Independent instrument: evaluate the k-fold mixed difference of each unit
directly at p_L + delta 1_S (exact Fractions, base B, step delta) and compare
with the prediction delta * lam(v_T, M(T)) * [(a) holds] used by mixed.c.
Also checks Lambda max_N = -delta*(-1)^k... (sign convention of mixed.py:
(-1)^{k-|S|}).  Usage: python3 direct_check.py N k
"""
import itertools, sys
from fractions import Fraction
sys.argv = sys.argv[:3]
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/ktie')
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import wk, mixed
import vocabulary_search as vs
N, k = wk.N, wk.k
units = list(wk.units())
Hmax = max(max(abs(x) for x in key[0]) for key, _ in units)
B = 2 * (Hmax + N) + 2
Cc = 1 + max(sum(abs(x) for x in key[0]) for key, _ in units) + 2 * N
delta = Fraction(1, 4 * Cc)
bad = 0; checked = 0; nonzero = 0
for key, cfg in units:
    h, M = key
    mu = [sum(1 for (i, j) in M if j == o) - h[o] for o in range(N)]
    for T in itertools.combinations(range(N), k):
        Ts = set(T); rest = [o for o in range(N) if o not in Ts]
        v = [h[t] + sum(1 for (i, j) in M if i == t and j not in Ts) for t in T]
        pos = {t: n for n, t in enumerate(T)}
        MT = [(pos[i], pos[j]) for (i, j) in M if i in Ts and j in Ts]
        lamv = mixed.lam(v, MT)
        nbr = {o: [] for o in range(N)}
        for i, j in M: nbr[i].append(j); nbr[j].append(i)
        for order in itertools.permutations(rest):
            p = [Fraction(0)] * N
            for r_, o in enumerate(order): p[o] = -Fraction(B) ** (r_ + 1)
            tot = Fraction(0); tm = Fraction(0)
            for bits in range(1 << k):
                x = list(p)
                for a in range(k):
                    if bits >> a & 1: x[T[a]] += delta
                sg = (-1) ** (k - bin(bits).count('1'))
                tot += sg * vs.eval_key(key, x); tm += sg * max(x)
            assert tm == (-1) ** (k + 1) * delta
            # condition (a)
            rk = {o: r_ for r_, o in enumerate(order)}
            ok = all(sum(1 for u in nbr[o] if u not in Ts and rk[u] > rk[o]) == mu[o] for o in rest)
            pred = delta * lamv if ok else 0
            checked += 1; nonzero += tot != 0
            if tot != pred: bad += 1
print(f'N={N} k={k}: units {len(units)}, (unit, locality) pairs {checked}, nonzero {nonzero}, mismatches {bad}')
