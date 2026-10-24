#!/usr/bin/env python3
"""Served k-sets of one caterpillar unit under the mixed difference.
Usage: python3 detail.py N k "S" "states"   e.g. detail.py 8 5 "1,2,3,5,6" "2,2,1,1,2,2"
"""
import sys, itertools, math
from fractions import Fraction
N, k = int(sys.argv[1]), int(sys.argv[2])
S = tuple(int(x) for x in sys.argv[3].split(','))
st = tuple(int(x) for x in sys.argv[4].split(','))
sys.argv = [sys.argv[0], str(N), str(k)]
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/ktie')
import wk, mixed
edges, last = wk.caterpillar(S)
lin = [(last, 0)]; M = []
for (a, b), s in zip(edges, st):
    if s == 1: lin.append((a, b))
    if s == 2:
        if a > b: lin.append((a, b)); a, b = b, a
        M.append((a, b))
import vocabulary_search as vs
h = vs.vec(N, lin)
mu = [sum(1 for (i, j) in M if j == o) - h[o] for o in range(N)]
deg = [sum(1 for e in M if o in e) for o in range(N)]
kap = [deg[o] - mu[o] for o in range(N)]
print('edges (parent,child,state):', [(a, b, s) for (a, b), s in zip(edges, st)], 'last', last)
print('kappa', kap, 'F', sorted(M))
tot = Fraction(0)
for T in itertools.combinations(range(N), k):
    Ts = set(T)
    v = [h[t] + sum(1 for (i, j) in M if i == t and j not in Ts) for t in T]
    pos = {t: n for n, t in enumerate(T)}
    MT = [(pos[i], pos[j]) for (i, j) in M if i in Ts and j in Ts]
    l = mixed.lam(v, MT)
    cnt = wk.count_orders(Ts, M, mu)
    if cnt:
        p = Fraction(cnt, math.factorial(N - k))
        print(T, 'p', p, 'v', v, 'MT', MT, 'Lambda', l)
        if l: tot += p
print('W =', tot)
