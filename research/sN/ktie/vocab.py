#!/usr/bin/env python3
"""Local vocabulary at k-ties: all local germs (v, M(T)) of units that serve
some k-locality (condition (a) for some order, germ depends on all T coords).
Keys are canonicalized under relabelling T (S_k) by brute force.
Usage: python3 vocab.py N k  -> data/lvocab_N_k.pkl, prints size and max|v|
"""
import itertools, sys, pickle, os
sys.argv = sys.argv[:3]
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/ktie')
import wk
N, k = wk.N, wk.k


def canon(v, MT):
    best = None
    for perm in itertools.permutations(range(k)):
        vv = [0] * k
        for a in range(k): vv[perm[a]] = v[a]
        mm = tuple(sorted(tuple(sorted((perm[i], perm[j]))) for i, j in MT))
        # orientation matters only up to linear terms: sigma(z_j - z_i) = sigma(z_i - z_j) - (z_i - z_j)
        # normalise each pair to (min,max) and adjust v
        vv2 = list(vv)
        for (i, j) in MT:
            a, b = perm[i], perm[j]
            if a > b:  # sigma(z_a - z_b) with a > b -> sigma(z_b - z_a) + (z_a - z_b)
                vv2[a] += 1; vv2[b] -= 1
        key = (tuple(vv2), mm)
        if best is None or key < best: best = key
    return best


vocab = set()
for key, cfg in wk.units():
    h, M = key
    mu = [sum(1 for (i, j) in M if j == o) - h[o] for o in range(N)]
    for T in itertools.combinations(range(N), k):
        Ts = set(T)
        v = [h[t] + sum(1 for (i, j) in M if i == t and j not in Ts) for t in T]
        pos = {t: n for n, t in enumerate(T)}
        MT = [(pos[i], pos[j]) for (i, j) in M if i in Ts and j in Ts]
        inc = {a for e in MT for a in e}
        if any(v[a] == 0 and a not in inc for a in range(k)): continue
        if not wk.count_orders(Ts, M, mu): continue
        vocab.add(canon(v, MT))
print(f'N={N} k={k}: local vocabulary {len(vocab)} classes; max|v| = {max(max(abs(x) for x in v) for v, _ in vocab)}')
os.makedirs('/home/jzimmermann/code/Max_Caterpillar/research/sN/ktie/data', exist_ok=True)
pickle.dump(sorted(vocab), open(f'/home/jzimmermann/code/Max_Caterpillar/research/sN/ktie/data/lvocab_{N}_{k}.pkl', 'wb'))
