"""Control for the single-apex lemma: for each apex a, units with apex a admit no
braid-linear combination with D_[N] != 0  <=>  D_[N] row lies in the row space of
the KINK rows restricted to those units (mod-P rank test; a 'lemma holds' answer
needs rank equality, which mod P can only *under*state -> treat as measured)."""
import sys, flint
from solve import System
P = 2147483629
N = int(sys.argv[1]); S = System(N)
def apex(k):
    h, M = k
    nodes = {i for e in M for i in e}
    c = [i for i in range(N) if h[i] == -1 and i not in nodes]
    return c
for a in range(N):
    units = [u for u, k in enumerate(S.U) if a in apex(S.U[u])]
    gis = sorted({gi for u in units for gi, _ in S.ug[u]})
    pos = {u: i for i, u in enumerate(units)}
    M = flint.nmod_mat(len(gis) + 1, len(units), P)
    for r, gi in enumerate(gis):
        for u, lam in S.groups[S.gkeys[gi]].items():
            if u in pos: M[r, pos[u]] = lam
    M0 = flint.nmod_mat(len(gis), len(units), P)
    for r, gi in enumerate(gis):
        for u, lam in S.groups[S.gkeys[gi]].items():
            if u in pos: M0[r, pos[u]] = lam
    for u in units: M[len(gis), pos[u]] = int(S.Dm[-1, u]) % P
    print('apex', a, 'units with this apex candidate', len(units), 'rank kink', M0.rank(), 'rank kink+Dtop', M.rank())
