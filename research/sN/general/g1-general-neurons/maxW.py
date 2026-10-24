"""Measured: maximal 3-locality passing weight W(g) = #passing localities/(N-3)! of ONE general
neuron (translation-invariant model A of research/sN/dfs/h4-general-neurons/passing.py:
symmetric weights a_ij of |x_i-x_j|, vertex values kappa).  Cheap test of how W grows with N:
W = O(N^2) would make the 3-locality method give Omega(N) for general neurons; W = Theta(N^3)
would make it give O(1).  Exact enumeration of all N! orders; hill climbing over a grid.
Usage: python maxW.py N iters seed"""
import sys, itertools, random
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/dfs/h4-general-neurons')
from passing import germ_passes

N = int(sys.argv[1]); iters = int(sys.argv[2]); seed = int(sys.argv[3])
rng = random.Random(seed)
PERM = np.array(list(itertools.permutations(range(N))), dtype=np.int64)
fact3 = 6 * np.prod(range(1, N - 2))
TRI = list(itertools.combinations(range(N), 3))
mask = np.tril(np.ones((N, N), bool), -1)  # q < r

def W(a2, kap2):
    """a2: integer matrix = 2*a (symmetric, zero diag); kap2 = 2*kappa (ints)."""
    Ap = a2[PERM[:, :, None], PERM[:, None, :]]          # P x N x N, Ap[p,r,q] = a2[pi_r, pi_q]
    S = (Ap * mask).sum(2)                                # weight to vertices above
    ok = (S[:, 3:] == kap2[PERM[:, 3:]]).all(1)
    if not ok.any():
        return 0.0, None
    good = {}
    for T in TRI:
        s = [Fr(int(kap2[t])) - sum(Fr(int(a2[t, u]), 2) for u in T) for t in T]
        aT = {(0, 1): Fr(int(a2[T[0], T[1]]), 2), (0, 2): Fr(int(a2[T[0], T[2]]), 2), (1, 2): Fr(int(a2[T[1], T[2]]), 2)}
        good[T] = germ_passes(s, aT)
    top = np.sort(PERM[:, :3], 1)
    gm = np.array([good[tuple(r)] for r in top])
    return (ok & gm).sum() / fact3, None

def rand_state():
    a2 = np.zeros((N, N), np.int64)
    for i in range(N):
        for j in range(i + 1, N):
            if rng.random() < 0.4:
                a2[i, j] = a2[j, i] = rng.choice([-2, -1, 1, 2])
    kap2 = np.array([rng.choice(range(-4, 5)) for _ in range(N)], np.int64)
    return a2, kap2

best = (0, None)
for it in range(iters):
    a2, k2 = rand_state(); w, _ = W(a2, k2)
    for step in range(400):
        b2, l2 = a2.copy(), k2.copy()
        if rng.random() < 0.5:
            i, j = rng.sample(range(N), 2); v = rng.choice([-2, -1, 0, 0, 1, 2]); b2[i, j] = b2[j, i] = v
        else:
            l2[rng.randrange(N)] = rng.choice(range(-4, 5))
        w2, _ = W(b2, l2)
        if w2 >= w:
            a2, k2, w = b2, l2, w2
    if w > best[0]:
        best = (w, (a2.copy(), k2.copy()))
        print('iter', it, 'W', w, 'C(N,3)', len(TRI), flush=True)
        print(best[1][0] / 2, best[1][1] / 2, flush=True)
print('N', N, 'best W', best[0], 'C(N,3)', len(TRI), 'method bound C(N,3)/W', len(TRI) / best[0] if best[0] else None)
