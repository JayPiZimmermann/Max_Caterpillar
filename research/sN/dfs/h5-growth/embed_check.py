"""Check: for 3 <= m < N, every non-auxiliary unit of K_0(m), embedded on any m-subset S of [N]
by an arbitrary injective relabelling (then normalized), is a non-auxiliary unit of K_0(N).
usage: python embed_check.py N"""
import itertools, sys
from kf import units_of
N = int(sys.argv[1])
UN = set(units_of(N))
def norm(h, prs):
    h = list(h); M = []
    for a, b in prs:
        if a > b:
            h[a] += 1; h[b] -= 1; a, b = b, a
        M.append((a, b))
    return (tuple(h), frozenset(M))
bad = 0; tot = 0
for m in range(3, N):
    Um = units_of(m)
    for S in itertools.permutations(range(N), m):
        for h, M in Um:
            H = [0] * N
            for i, s in enumerate(S):
                H[s] = h[i]
            k = norm(H, [(S[a], S[b]) for a, b in M])
            tot += 1
            if k not in UN:
                bad += 1
print('N', N, 'embedded keys checked', tot, 'missing', bad)
