"""Images of grade-j keys in gr_j = F_j/F_{j-1} (F_j = A_N + span{U_k : |M_k| <= j}).
Reports rank of gr_j, #keys, #zero images, #parallel classes, class-size histogram, and support
size histogram of image vectors in the pivot basis.  Mod-p (measured).  Usage: parclass.py N"""
import sys, collections
import numpy as np
from common import keys, vs
from sym import eval_keys
P = vs.P
N = int(sys.argv[1]); ks = keys(N); DUMP = [int(t) for t in sys.argv[2:]]
aux = []
for i in range(N):
    for s in (1, -1):
        e = [0] * N; e[i] = s; aux.append((tuple(e), frozenset()))
for i in range(N):
    for j in range(i + 1, N):
        e = [0] * N; e[i] = 1; e[j] = -1; aux.append((tuple(e), frozenset()))
fam = aux + sorted(ks, key=lambda k: len(k[1]))
gr = [-1] * len(aux) + [len(k[1]) for k in fam[len(aux):]]
rng = np.random.default_rng(3)
X = rng.integers(-10**6, 10**6, size=(len(fam) + 40, N), endpoint=True).astype(np.int64)
E = eval_keys(fam, X).T            # points x functions
R, piv = vs.rref_mod_p(E)
prow = {c: r for r, c in enumerate(piv)}
for j in sorted(set(gr) - {-1}):
    cols = [c for c in range(len(fam)) if gr[c] == j]
    jp = [c for c in cols if c in prow]
    rows = [prow[c] for c in jp]
    vecs = {}
    zero = 0; supp = collections.Counter()
    for c in cols:
        v = R[rows, c] % P
        nz = np.nonzero(v)[0]
        if len(nz) == 0: zero += 1; continue
        supp[len(nz)] += 1
        v = v * pow(int(v[nz[0]]), P - 2, P) % P
        vecs.setdefault(v.tobytes(), []).append(fam[c])
    hist = collections.Counter(len(x) for x in vecs.values())
    if j in DUMP:
        for v, L in vecs.items():
            if len(L) > 1: print("   class", [(k[0], sorted(k[1])) for k in L])
    print(f'N={N} grade |M|={j}: keys {len(cols)} rank {len(jp)} zero-images {zero} parallel classes {len(vecs)} class sizes {sorted(hist.items())} support sizes {sorted(supp.items())[:12]}')
