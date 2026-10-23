#!/usr/bin/env python3
"""Find a small set of S_m-orbit germ types from a family (pn_test conventions) whose orbit sums
span max_m (mod linear + aux), by backward elimination with mod-p rank tests.
Usage: pn_solve.py m R mode"""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from pn_test import forests, is_ham_path, is_spanning, heads, rank_mod_p, P

def family(m, R, mode):
    rest = list(range(1, m)); Fs = forests(rest)
    sel = {'all': lambda F: True, 'nopath': lambda F: not is_ham_path(F, rest),
           'top_nopath': lambda F: is_spanning(F, rest) and not is_ham_path(F, rest)}[mode]
    perms = list(itertools.permutations(rest)); seen = set(); fams = []
    for F in Fs:
        if not sel(F): continue
        for v in heads(m, 0, R):
            best = None
            for p in perms:
                mp = {0: 0}; mp.update(dict(zip(rest, p)))
                vv = [0] * m
                for t in range(m): vv[mp[t]] = v[t]
                FF = tuple(sorted(tuple(sorted((mp[u], mp[w]))) for u, w in F))
                key = (tuple(vv), FF)
                if best is None or key < best: best = key
            if best not in seen: seen.add(best); fams.append(best)
    return fams

def evalcols(m, fams, X):
    allp = list(itertools.permutations(range(m)))
    cols = []
    for (v, F) in fams:
        v = np.array(v); tot = np.zeros(len(X), dtype=np.int64)
        for p in allp:
            Z = X[:, p]; s = Z @ v
            for (i, j) in F: s = s + np.maximum(Z[:, i] - Z[:, j], 0)
            tot += np.maximum(s, 0)
        cols.append(tot)
    return cols

def main():
    m, R, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    fams = family(m, R, mode)
    rng = np.random.default_rng(7)
    X = rng.integers(-10**4, 10**4, size=(len(fams) + 80, m))
    cols = evalcols(m, fams, X)
    aux = sum(np.maximum(X[:, i] - X[:, j], 0) for i in range(m) for j in range(m) if i != j)
    lin = X.sum(axis=1); mx = X.max(axis=1)
    base = [aux, lin]
    def inspan(idx):
        B = np.stack([cols[i] for i in idx] + base, axis=1)
        return rank_mod_p(np.concatenate([B, mx[:, None]], axis=1)) == rank_mod_p(B)
    idx = list(range(len(fams)))
    assert inspan(idx), 'max not in span'
    # backward elimination, try removing large-head / many-hinge types first
    order = sorted(idx, key=lambda i: (-max(abs(x) for x in fams[i][0]), -len(fams[i][1])))
    keep = set(idx)
    # coarse: remove chunks
    chunk = max(1, len(order) // 16)
    pos = 0
    while pos < len(order):
        ch = [i for i in order[pos:pos + chunk] if i in keep]
        trial = sorted(keep - set(ch))
        if ch and inspan(trial):
            keep -= set(ch)
        elif len(ch) > 1:
            for i in ch:
                trial = sorted(keep - {i})
                if inspan(trial): keep.discard(i)
        pos += chunk
    keep = sorted(keep)
    print(f'm={m} R={R} mode={mode}: {len(fams)} types; minimal-by-elimination support {len(keep)} types:')
    for i in keep: print('  v =', fams[i][0], ' F =', fams[i][1])

if __name__ == '__main__':
    main()
