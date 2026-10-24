import sys, itertools, time, math
from fractions import Fraction
from germs import localities, relabel
from local import full_matrix, quotient_modp, in_span, rank_p
import numpy as np
m = int(sys.argv[1]); Ns = [int(a) for a in sys.argv[2].split(',')]
for N in Ns:
    t0=time.time()
    G = set()
    for uid, cfg, T, c, g in localities(N, m):
        G.add(g)
    Gc = set()
    for g in G:
        for perm in itertools.permutations(range(m)):
            Gc.add(relabel(g, perm))
    print(f'N={N} m={m}: raw germs {len(G)}, S_m-closed {len(Gc)} ({time.time()-t0:.1f}s)', flush=True)
germs = sorted(Gc, key=lambda k:(sorted(k[1]), k[0]))
A, naux = full_matrix(m, germs)
Q = quotient_modp(A, naux)
n = len(germs)
nonaux = [i for i in range(n) if Q[:, i].any()]
print('quotient rank', rank_p(Q), 'rows', Q.shape[0], 'nonaux germs', len(nonaux), 'max in span(all)', in_span(Q, nonaux))
for s in range(1, 4):
    found = None; cnt=0
    for S in itertools.combinations(nonaux, s):
        if in_span(Q, S):
            found = S; break
    print('size', s, 'found', found and [germs[i] for i in found], flush=True)
    if found: break
