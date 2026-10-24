#!/usr/bin/env python3
"""k-tie localities: per-unit weight W_k and the local vocabulary.

For a caterpillar face unit U_{h,M} (identity labelling, apex 0, as in
count_ab.py) and a k-set T, the locality (T, rho) has T tied at 0 and the
outside coordinates strictly below in the order rho.  The unit is nonlinear
there only if (a): every outside o has exactly mu_o = |N^-(o)| - h_o hinge
neighbours below it.  p_T = fraction of the (N-k)! orders satisfying (a).
The local unit is sigma(<v,y_T> + sum_{(i,j) in M(T)} sigma(y_i - y_j)),
v_t = h_t + |N^+(t) \\ T|.  W_k(unit) = sum_T p_T [local class != 0 mod aux_k].

Usage: python3 wk.py N k   -> prints max W_k, histogram, local vocabulary size,
and pickles (local vocabulary, nontrivial flags) to data/.
"""
import itertools, math, sys, pickle, os
from fractions import Fraction
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs

N = int(sys.argv[1]); k = int(sys.argv[2])
r = N - 2
HERE = os.path.dirname(os.path.abspath(__file__))


def caterpillar(S):
    edges = []
    for j in range(1, r + 1):
        p = max([0] + [i for i in S if i < j])
        edges.append((p + 1, j + 1))
    return edges, max(S) + 1


def units():
    seen = set()
    for size in range(1, r + 1):
        for S in itertools.combinations(range(1, r + 1), size):
            edges, last = caterpillar(S)
            for states in itertools.product(range(3), repeat=r):
                lin = [(last, 0)]; M = []
                for (a, b), s in zip(edges, states):
                    if s == 1: lin.append((a, b))
                    if s == 2:
                        if a > b: lin.append((a, b)); a, b = b, a
                        M.append((a, b))
                key = (vs.vec(N, lin), frozenset(M))
                if key in seen or vs.is_auxiliary(key): continue
                seen.add(key)
                yield key, (S, states)


_triv = {}
def local_nontrivial(lkey):
    if lkey not in _triv:
        aux = vs.aux_functions(k)
        funcs = [('aux', a) for a in aux] + [('key', lkey)]
        rk, ok = vs.exact_rank_fast(k, funcs)
        assert ok
        _triv[lkey] = rk == len(funcs)
    return _triv[lkey]


def count_orders(T, M, mu):
    rest = [o for o in range(N) if o not in T]
    nbr = {o: [] for o in range(N)}
    for i, j in M:
        nbr[i].append(j); nbr[j].append(i)
    if any(mu[o] < 0 or mu[o] > len(nbr[o]) for o in rest):
        return 0
    idx = {o: t for t, o in enumerate(rest)}
    count = {0: 1}
    for _ in range(len(rest)):
        new = {}
        for placed, c in count.items():
            for o in rest:
                b = 1 << idx[o]
                if placed & b: continue
                below = sum(1 for u in nbr[o] if u not in T and not placed & (1 << idx[u]))
                if below == mu[o]:
                    new[placed | b] = new.get(placed | b, 0) + c
        count = new
    return sum(count.values())


if __name__ == '__main__':
    f = math.factorial(N - k)
    best = Fraction(0); bestcfg = None; hist = {}
    vocab = {}
    for key, cfg in units():
        h, M = key
        mu = [sum(1 for (i, j) in M if j == o) - h[o] for o in range(N)]
        W = Fraction(0); detail = []
        for T in itertools.combinations(range(N), k):
            Ts = set(T)
            cnt = count_orders(Ts, M, mu)
            if not cnt: continue
            v = [h[t] + sum(1 for (i, j) in M if i == t and j not in Ts) for t in T]
            pos = {t: n for n, t in enumerate(T)}
            MT = frozenset((pos[i], pos[j]) for (i, j) in M if i in Ts and j in Ts)
            lkey = (tuple(v), MT)
            if not local_nontrivial(lkey): continue
            vocab[lkey] = vocab.get(lkey, 0) + 1
            W += Fraction(cnt, f); detail.append((T, Fraction(cnt, f)))
        hist[W] = hist.get(W, 0) + 1
        if W > best: best, bestcfg = W, (key, cfg, detail)
    nloc = math.comb(N, k)
    print(f'N={N} k={k}: max W_k = {best} ({float(best):.4f}); C(N,k) = {nloc}; '
          f'C(N,k)/maxW = {float(nloc / best) if best else "inf"} (times s\'_k)')
    print('  argmax:', bestcfg[1], bestcfg[2] if bestcfg else None)
    print('  #local vocabulary keys:', len(vocab))
    print('  histogram:', {str(a): b for a, b in sorted(hist.items())})
    os.makedirs(os.path.join(HERE, 'data'), exist_ok=True)
    pickle.dump(vocab, open(os.path.join(HERE, 'data', f'vocab_{N}_{k}.pkl'), 'wb'))
