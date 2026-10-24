"""Do the faces of the caterpillars of a few labelings pi suffice?
For a set P of permutations, let U(P) = normalized face keys of all (pi, S, tau), pi in P.
Test (mod P rank): is there a braid-linear combination of U(P) with D_[N] != 0
('top') / an expansion of max_N ('full')?  Search: greedy growth of P by random
permutations until feasible; report |P| and |U(P)|.
usage: python fewperm.py N mode trials seed
"""
import itertools
import random
import sys

import flint

from solve import System
import vocabulary_search as vs

PR = 2147483629
N, MODE, TRIALS, SEED = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
S = System(N)
idx = {k: i for i, k in enumerate(S.U)}
SR = [S.Dm.shape[0] - 1] if MODE == 'top' else list(range(S.Dm.shape[0]))
r = N - 2


def faces_of_pi(pi):
    out = set()
    for size in range(1, r + 1):
        for Sc in itertools.combinations(range(1, r + 1), size):
            for k in vs.normalized_faces(N, pi, frozenset(Sc)):
                if k in idx:
                    out.add(idx[k])
    return out


def feasible(units):
    import numpy as np
    units = sorted(units)
    pos = {u: i for i, u in enumerate(units)}
    gis = sorted({gi for u in units for gi, _ in S.ug[u]})
    m = len(units)
    A = np.zeros((len(gis) + len(SR), m + 1), dtype=np.int64)
    for rr, gi in enumerate(gis):
        for u, lam in S.groups[S.gkeys[gi]].items():
            if u in pos:
                A[rr, pos[u]] = lam
    for t, s in enumerate(SR):
        A[len(gis) + t, :m] = S.Dm[s, units]
        A[len(gis) + t, m] = S.tD[s]
    A %= PR
    full = flint.nmod_mat(A.shape[0], m + 1, A.ravel().tolist(), PR).rank()
    left = flint.nmod_mat(A.shape[0], m, A[:, :m].ravel().tolist(), PR).rank()
    return left == full


rng = random.Random(SEED)
perms = list(itertools.permutations(range(N)))
for trial in range(TRIALS):
    rng.shuffle(perms)
    P, U = [], set()
    for pi in perms:
        P.append(pi)
        U |= faces_of_pi(pi)
        if len(P) >= N - 2 and (len(P) < 12 or len(P) % 6 == 0):
            ok = feasible(U)
            print('   |P|', len(P), '|U|', len(U), ok, flush=True)
            if ok:
                break
    print(f'trial {trial}: feasible after {len(P)} labelings, {len(U)} units; P = {P}', flush=True)
