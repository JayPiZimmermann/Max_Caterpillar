"""t*_m: min number of FULL germs (depending on all m variables) needed so that
max_m in span(S + all non-full germs of the class + aux).  W_full(N): max over units
of the weighted number of m-localities where the unit's germ is full.
Bound: s_N >= t*_m * C(N,m) / W_full_m(N)."""
import sys, itertools, time, math
from fractions import Fraction
import numpy as np
from germs import localities, relabel
import vocabulary_search as vs
from local import full_matrix, rank_p
P = vs.P
m = int(sys.argv[1]); N = int(sys.argv[2]); smax = int(sys.argv[3]) if len(sys.argv) > 3 else 3

def isfull(g):
    h, M = g
    return all(h[t] != 0 or any(t in e for e in M) for t in range(len(h)))

rec = list(localities(N, m))
G = {g for *_, g in rec}
Gc = set()
for g in G:
    for perm in itertools.permutations(range(m)):
        Gc.add(relabel(g, perm))
nonfull = sorted([g for g in Gc if not isfull(g)], key=str)
full = sorted([g for g in Gc if isfull(g)], key=str)
W = {}
for uid, cfg, T, c, g in rec:
    if isfull(g):
        W[uid] = W.get(uid, 0) + Fraction(c, math.factorial(N - m))
best = max(W.values())
print(f"N={N} m={m}: class {len(Gc)} full {len(full)} nonfull {len(nonfull)}; W_full={best} C/W={math.comb(N,m)/best:.4f}", flush=True)
# quotient: eliminate aux + nonfull columns first
A, naux = full_matrix(m, nonfull + full)
nel = naux + len(nonfull)
R, piv = vs.rref_mod_p(np.array(A, dtype=np.int64))
keep = [i for i, c in enumerate(piv) if c >= nel]
Q = R[keep][:, nel:] % P
print('quotient rows', Q.shape[0], 'max column zero?', not Q[:, -1].any(), flush=True)
def in_span(S):
    sub = Q[:, list(S)]
    return rank_p(np.hstack([sub, Q[:, -1:]])) == rank_p(sub)
nz = [i for i in range(len(full)) if Q[:, i].any()]
print('full germs nonzero in quotient', len(nz))
for s in range(1, smax + 1):
    found = None
    for S in itertools.combinations(nz, s):
        if in_span(S):
            found = S; break
    print('size', s, 'found', found and [full[i] for i in found], flush=True)
    if found: break
