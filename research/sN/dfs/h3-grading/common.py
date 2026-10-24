"""Shared helpers for the h3-grading branch.
Dictionary = normalized caterpillar face descriptions K_0 (scripts/vocabulary_search.dictionary),
minus those that are auxiliary functions.  U_{h,M} is the support function of
Q_{h,M} = conv({0} u (h + Z_M)), Z_M = sum_{(i,j) in M} [0, e_i - e_j]."""
import sys, os, pickle, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', '..', 'scripts'))
import vocabulary_search as vs

def components(N, M):
    par = list(range(N))
    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for i, j in M:
        par[f(i)] = f(j)
    comp = {}
    for v in range(N):
        comp.setdefault(f(v), []).append(v)
    return list(comp.values())

def polydim(key):
    """dim conv(0, h + Z_M): |M| (M is a forest) plus 1 unless h in span(M) (h sums to 0 on every component)."""
    h, M = key
    N = len(h)
    inaff = all(sum(h[v] for v in C) == 0 for C in components(N, M))
    return len(M) + (0 if inaff else 1)

def keys(N):
    cache = os.path.join(HERE, f'keys_{N}.pkl')
    if os.path.exists(cache):
        return pickle.load(open(cache, 'rb'))
    K0, _ = vs.dictionary(N)
    ks = sorted((k for k in K0 if not vs.is_auxiliary(k)), key=lambda k: (k[0], sorted(k[1])))
    pickle.dump(ks, open(cache, 'wb'))
    return ks
