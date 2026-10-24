#!/usr/bin/env python3
"""Build exact test matrices (apex-0 keys of the class-G tree vocabulary and of the
caterpillar dictionary) and report per-unit maxima w_m = max_k #passed classes of size m / (N-m)!.
Usage: build.py N   -> writes tests_N.pkl"""
import sys, pickle, math, itertools
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs
import loctests as L
N = int(sys.argv[1])
cls = L.classes(N)
G = sorted(k for k in L.tc.vocabulary(N, 'G') if k[0][0] == -1 and all(0 not in e for e in k[1]))
K0, _ = vs.dictionary(N)
cat = set(k for k in K0 if not vs.is_auxiliary(k))
rows = {}
for k in G:
    v = tuple(L.delta(k, N, T, o) for T, o in cls)
    rows[k] = v
catall = sorted(cat)
catrows = {k: tuple(L.delta(k, N, T, o) for T, o in cls) for k in catall}
pickle.dump({'N': N, 'classes': cls, 'G': rows, 'cat': catrows}, open(f'tests_{N}.pkl', 'wb'))
def report(name, R):
    for m in range(3, N + 1):
        idx = [i for i, (T, o) in enumerate(cls) if len(T) == m]
        best = max(R.items(), key=lambda kv: sum(1 for i in idx if kv[1][i]))
        cnt = sum(1 for i in idx if best[1][i])
        print(f'  {name} m={m}: max passed classes {cnt} = {cnt / math.factorial(N - m)} (N-m)!  C(N-2,m-2)={math.comb(N-2,m-2)}  key={best[0][0]} {sorted(best[0][1])}')
print(f'N={N}: classes {len(cls)}, G apex-0 keys {len(G)}, caterpillar keys {len(catall)} (all apices)')
report('G  ', rows); report('cat', catrows)
print('caterpillar keys with apex 0 in G-set:', sum(1 for k in catall if k in rows), '/', sum(1 for k in catall if k[0][0] == -1 and all(0 not in e for e in k[1])))
