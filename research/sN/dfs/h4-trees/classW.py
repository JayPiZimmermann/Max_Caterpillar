#!/usr/bin/env python3
"""max over units of a tree class of w_m(u) (branch h4-trees).
Usage: python classW.py N mode     (mode as in treeclass: out/in/G/star; plus pc/cp)
 pc: tree rooted at rho, generators e_parent - e_child, head at ANY vertex r
     (contains the caterpillar family);
 cp: generators e_child - e_parent, head at any vertex (contains out-stars).
Units are canonicalised by (sorted kappa multiset, forest degree data) only for
deduplication of identical (nbr, kappa) pairs; apex fixed to label 0 by symmetry."""
import sys, itertools
from fractions import Fraction
import treeclass as tc
import wcount as wc

def class_keys(N, mode):
    a = 0
    vs = list(range(1, N))
    for edges in tc.pruefer_trees(vs):
        if mode == 'star' and not tc.is_star(edges): continue
        for rho in vs:
            pcs = tc.orient_from(edges, rho)
            for r in vs:
                if mode in ('pc', 'cp'):
                    gens = [(p, c) if mode == 'pc' else (c, p) for p, c in pcs]
                    for st in itertools.product(range(3), repeat=len(gens)):
                        lin = [(r, a)] + [g for g, s in zip(gens, st) if s == 1]
                        hin = [g for g, s in zip(gens, st) if s == 2]
                        yield tc.norm(N, lin, hin)
                else:
                    if rho != vs[0]: continue
                    for k in tc.faces(N, a, edges, r, 'G' if mode == 'star' else mode):
                        yield k

if __name__ == '__main__':
    N = int(sys.argv[1]); mode = sys.argv[2]
    seen = set(); best = [Fraction(0)] * (N + 1); arg = [None] * (N + 1)
    for k in class_keys(N, mode):
        n, nbr, kappa = wc.key_to_unit(k)
        sig = (tuple(nbr), tuple(kappa))
        if sig in seen: continue
        seen.add(sig)
        w = wc.weights(n, nbr, kappa, 3)
        for m in range(3, N + 1):
            if w[m] > best[m]: best[m] = w[m]; arg[m] = k
    print(f'N={N} mode={mode}: {len(seen)} distinct (F,kappa)')
    for m in range(3, N + 1):
        h, M = arg[m] if arg[m] else (None, None)
        print(f'  m={m}: max w_m = {best[m]} = {float(best[m]):.4f}   (6^m={6**m});  argmax h={h} M={sorted(M) if M else M}')
