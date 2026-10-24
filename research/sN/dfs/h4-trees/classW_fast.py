#!/usr/bin/env python3
"""max over units of a tree class of w_m(u), unlabeled trees, C backend (h4-trees).
Usage: python classW_fast.py N mode [dump]
modes: pc (rooted tree, generators e_parent - e_child, head anywhere; contains
the caterpillar family), cp (generators e_child - e_parent, head anywhere;
contains out-stars), G (all orientations, all heads), cat (caterpillar family only).
Prints max_u w_m(u) and the ratio max w_m^(1/m)."""
import sys, itertools, subprocess
from fractions import Fraction
from math import factorial
import treeclass as tc
import wcount as wc
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')

def canon(n_vs, edges, vs):
    adj = {v: [] for v in vs}
    for u, w in edges: adj[u].append(w); adj[w].append(u)
    def enc(v, p):
        return '(' + ''.join(sorted(enc(w, v) for w in adj[v] if w != p)) + ')'
    return min(enc(v, None) for v in vs)

def free_trees(vs):
    seen = {}
    for edges in tc.pruefer_trees(vs):
        c = canon(len(vs), edges, vs)
        if c not in seen: seen[c] = edges
    return list(seen.values())

def keys(N, mode):
    a = 0; vs = list(range(1, N))
    if mode == 'cat':
        sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
        import vocabulary_search as vsr
        r = N - 2
        pi = tuple(range(N))
        for size in range(1, r + 1):
            for S in itertools.combinations(range(1, r + 1), size):
                for k in vsr.normalized_faces(N, pi, frozenset(S)):
                    yield k
        return
    for edges in free_trees(vs):
        for rho in vs:
            pcs = tc.orient_from(edges, rho)
            for r in vs:
                if mode in ('pc', 'cp'):
                    gens = [(p, c) if mode == 'pc' else (c, p) for p, c in pcs]
                    for st in itertools.product(range(3), repeat=len(gens)):
                        lin = [(r, a)] + [g for g, s in zip(gens, st) if s == 1]
                        hin = [g for g, s in zip(gens, st) if s == 2]
                        yield tc.norm(N, lin, hin)
                elif mode == 'G':
                    if rho != vs[0]: continue
                    for k in tc.faces(N, a, edges, r, 'G'):
                        yield k

def run(N, mode):
    sigs = {}
    for k in keys(N, mode):
        n, nbr, kappa = wc.key_to_unit(k)
        sig = (tuple(nbr), tuple(kappa))
        if sig not in sigs: sigs[sig] = k
    lst = list(sigs.items())
    inp = ''.join(f'{N} ' + ' '.join(map(str, s[0])) + ' ' + ' '.join(map(str, s[1])) + '\n' for s, _ in lst)
    out = subprocess.run(['./wfast'], input=inp, capture_output=True, text=True, check=True).stdout.split('\n')
    best = [Fraction(0)] * (N + 1); arg = [None] * (N + 1); allw = []
    for (s, k), line in zip(lst, out):
        c = list(map(int, line.split()))
        w = [Fraction(c[m], factorial(N - m)) for m in range(N + 1)]
        allw.append((k, w))
        for m in range(3, N + 1):
            if w[m] > best[m]: best[m] = w[m]; arg[m] = k
    return lst, best, arg, allw

if __name__ == '__main__':
    N = int(sys.argv[1]); mode = sys.argv[2]
    lst, best, arg, allw = run(N, mode)
    print(f'N={N} mode={mode}: {len(lst)} distinct (F,kappa) signatures')
    for m in range(3, N + 1):
        h, M = arg[m]
        _, nbr, kap = wc.key_to_unit(arg[m])
        print(f'  m={m}: max w_m = {best[m]} = {float(best[m]):.4f}, (max w_m)^(1/m) = {float(best[m])**(1/m):.4f};'
              f' kappa={kap} M={sorted(M)}', flush=True)
