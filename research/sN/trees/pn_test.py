#!/usr/bin/env python3
"""Germ-span tests at an m-tie (research/sN/trees).

Germ of a tree unit at a tie set T (|T| = m) with apex a in T:
    G(a, v, F)(z) = relu(<v, z> + sum_{(i,j) in F} relu(z_i - z_j)),
F a forest on T \\ {a}, v integer, v_a = -1, sum v = 0.
Question PN_m(shape filter): is max_m in span{G : F allowed} + linear + span relu(z_i - z_j)?
Everything is symmetrised over S_m (max_m is symmetric, the families are S_m-invariant),
so max_m is in the span iff it is in the span of the orbit sums.
Instrument: rank mod p of the evaluation matrix at random integer points (measured, not certified).
Usage: pn_test.py m R mode    mode in {all, nopath, lower, onlypath, nostar}
"""
import sys, itertools, random
import numpy as np

P = 2147483629  # prime < 2^31


def forests(vs):
    vs = list(vs)
    E = list(itertools.combinations(vs, 2))
    out = []
    for r in range(len(vs)):
        for F in itertools.combinations(E, r):
            # acyclic check by union-find
            par = {v: v for v in vs}
            def f(x):
                while par[x] != x:
                    x = par[x]
                return x
            ok = True
            for u, w in F:
                a, b = f(u), f(w)
                if a == b:
                    ok = False; break
                par[a] = b
            if ok:
                out.append(F)
    return out


def is_ham_path(F, vs):
    if len(F) != len(vs) - 1:
        return False
    deg = {v: 0 for v in vs}
    for u, w in F:
        deg[u] += 1; deg[w] += 1
    return max(deg.values()) <= 2


def is_spanning(F, vs):
    return len(F) == len(vs) - 1


def heads(m, a, R):
    others = [t for t in range(m) if t != a]
    for vals in itertools.product(range(-R, R + 1), repeat=m - 1):
        if sum(vals) != 1:
            continue
        v = [0] * m
        v[a] = -1
        for t, x in zip(others, vals):
            v[t] = x
        yield tuple(v)


def rank_mod_p(A):
    A = A.copy() % P
    m, n = A.shape
    r = 0
    for c in range(n):
        if r == m:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy(); col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            A[nzr] = (A[nzr] - (col[nzr, None] * A[r][None, :]) % P) % P
        r += 1
    return r


def main():
    m, R, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    npts = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    a = 0
    rest = list(range(1, m))
    Fs = forests(rest)
    if mode == 'all':
        Fs2 = Fs
    elif mode == 'nopath':
        Fs2 = [F for F in Fs if not is_ham_path(F, rest)]
    elif mode == 'lower':
        Fs2 = [F for F in Fs if not is_spanning(F, rest)]
    elif mode == 'onlypath':
        Fs2 = [F for F in Fs if is_ham_path(F, rest) or not is_spanning(F, rest)]
    elif mode == 'nostar':
        Fs2 = [F for F in Fs if not (is_spanning(F, rest) and max(
            sum(1 for e in F if v in e) for v in rest) == len(rest) - 1)]
    else:
        raise SystemExit('mode?')
    # dedupe (v,F) up to permutations of rest fixing a: canonical form
    perms = list(itertools.permutations(rest))
    seen = set(); fams = []
    for F in Fs2:
        for v in heads(m, a, R):
            best = None
            for p in perms:
                mp = {0: 0}
                for x, y in zip(rest, p):
                    mp[x] = y
                vv = [0] * m
                for t in range(m):
                    vv[mp[t]] = v[t]
                FF = tuple(sorted(tuple(sorted((mp[u], mp[w]))) for u, w in F))
                key = (tuple(vv), FF)
                if best is None or key < best:
                    best = key
            if best not in seen:
                seen.add(best); fams.append(best)
    nf = len(fams)
    print(f'm={m} R={R} mode={mode}: {len(Fs2)} forests, {nf} germ types (apex 0, up to S_(m-1))', flush=True)
    allp = list(itertools.permutations(range(m)))
    rng = np.random.default_rng(1)
    if npts == 0:
        npts = nf + 60
    X = rng.integers(-10**4, 10**4, size=(npts, m))
    # permuted points: Xp[k] = X[:, perm]
    cols = []
    for (v, F) in fams:
        v = np.array(v)
        tot = np.zeros(npts, dtype=np.int64)
        for p in allp:
            Z = X[:, p]
            s = Z @ v
            for (i, j) in F:
                s = s + np.maximum(Z[:, i] - Z[:, j], 0)
            tot += np.maximum(s, 0)
        cols.append(tot)
    # aux orbit sums (translation-invariant part) and linear
    aux = np.zeros(npts, dtype=np.int64)
    for i in range(m):
        for j in range(m):
            if i != j:
                aux += np.maximum(X[:, i] - X[:, j], 0)
    lin = X.sum(axis=1)
    mx = X.max(axis=1)
    B = np.stack(cols + [aux, lin], axis=1)
    rB = rank_mod_p(B)
    rBM = rank_mod_p(np.concatenate([B, mx[:, None]], axis=1))
    print(f'  rank(W+aux+lin) = {rB} (cols {B.shape[1]}, pts {npts}); with max: {rBM}  ->  max {"NOT in" if rBM > rB else "IN"} span', flush=True)


if __name__ == '__main__':
    main()
