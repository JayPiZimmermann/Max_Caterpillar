"""Export the kink system for the C++ circuit search (edfs.cpp).
Format: n G nS ; per unit: Dtop then D values for all |S|>=3 rows ; groups: size then (u lam)* ;
then nperm and the permutation table (unit index images)."""
import sys, itertools
sys.path.insert(0, '.')
from solve import System
N = int(sys.argv[1]); S = System(N)
def norm(h, pairs):
    h = list(h); M = []
    for a, b in pairs:
        if a > b:
            h[a] += 1; h[b] -= 1; a, b = b, a
        M.append((a, b))
    return (tuple(h), frozenset(M))
def permute_key(key, perm):
    h, M = key
    h2 = [0] * N
    for i in range(N): h2[perm[i]] = h[i]
    return norm(h2, [(perm[a], perm[b]) for a, b in M])
idx = {k: i for i, k in enumerate(S.U)}
perms = list(itertools.permutations(range(N)))
with open(f'data/edfs_{N}.txt', 'w') as f:
    nS = S.Dm.shape[0]
    f.write(f'{S.n} {len(S.gkeys)} {nS}\n')
    for u in range(S.n):
        f.write(' '.join(str(int(S.Dm[s, u])) for s in range(nS)) + '\n')
    for g in S.gkeys:
        grp = S.groups[g]
        f.write(str(len(grp)) + ' ' + ' '.join(f'{u} {l}' for u, l in grp.items()) + '\n')
    f.write(f'{len(perms)}\n')
    for p in perms:
        f.write(' '.join(str(idx[permute_key(k, p)]) for k in S.U) + '\n')
print('exported', S.n, len(S.gkeys))
