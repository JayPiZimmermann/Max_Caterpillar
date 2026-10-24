"""For apex sets A (|A| = r): units having an apex candidate in A.  Is there a
braid-linear combination with D_[N] != 0 among them?  (mod-P rank test: 'yes'
if rank(KINK+Dtop) > rank(KINK) mod P is a certified 'yes' only after an exact
solve; 'no' is measured.)"""
import sys, itertools, flint
from solve import System
P = 2147483629
N = int(sys.argv[1]); S = System(N)
def apexes(k):
    h, M = k
    nodes = {i for e in M for i in e}
    return {i for i in range(N) if h[i] == -1 and i not in nodes}
for r in range(1, N + 1):
    A = set(range(r))
    units = [u for u in range(S.n) if apexes(S.U[u]) & A]
    gis = sorted({gi for u in units for gi, _ in S.ug[u]})
    pos = {u: i for i, u in enumerate(units)}
    def mk(withD):
        M = flint.nmod_mat(len(gis) + withD, len(units), P)
        for rr, gi in enumerate(gis):
            for u, lam in S.groups[S.gkeys[gi]].items():
                if u in pos: M[rr, pos[u]] = lam
        if withD:
            for u in units: M[len(gis), pos[u]] = int(S.Dm[-1, u]) % P
        return M
    print('N', N, 'apex set size', r, 'units', len(units), 'D-active braid-linear combo exists (mod P):', mk(1).rank() > mk(0).rank(), flush=True)
