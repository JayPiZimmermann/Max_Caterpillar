"""Exact 3-locality passing weight W (= #passing localities/(N-3)!) of structured general neurons,
then hill climbing seeded from the best structured one (same model as maxW.py).
Usage: python star_W.py N climb_steps seed"""
import sys, itertools, random
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/dfs/h4-general-neurons')
from passing import germ_passes
N = int(sys.argv[1]); steps = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
PERM = np.array(list(itertools.permutations(range(N))), dtype=np.int64)
fact3 = 6 * int(np.prod(range(1, N - 2)))
TRI = list(itertools.combinations(range(N), 3))
mask = np.tril(np.ones((N, N), bool), -1)
top = np.sort(PERM[:, :3], 1); triidx = {T: i for i, T in enumerate(TRI)}
topi = np.array([triidx[tuple(r)] for r in top])
def W(a2, kap2):
    Ap = a2[PERM[:, :, None], PERM[:, None, :]]
    S = (Ap * mask).sum(2)
    ok = (S[:, 3:] == kap2[PERM[:, 3:]]).all(1)
    if not ok.any(): return 0.0
    good = np.zeros(len(TRI), bool)
    for i in set(topi[ok].tolist()):
        T = TRI[i]
        s = [Fr(int(kap2[t])) - sum(Fr(int(a2[t, u]), 2) for u in T) for t in T]
        aT = {(0, 1): Fr(int(a2[T[0], T[1]]), 2), (0, 2): Fr(int(a2[T[0], T[2]]), 2), (1, 2): Fr(int(a2[T[1], T[2]]), 2)}
        good[i] = germ_passes(s, aT)
    return (ok & good[topi]).sum() / fact3
cands = {}
for ka in range(-6, 7):            # star at 0, leaves alternate +1/-1 (a2 = +-2), kappa_leaf = a_leaf
    a2 = np.zeros((N, N), np.int64); k2 = np.zeros(N, np.int64)
    for j in range(1, N):
        v = 2 if j % 2 else -2; a2[0, j] = a2[j, 0] = v; k2[j] = v
    k2[0] = ka; cands[('star', ka)] = (a2, k2)
best = max(cands, key=lambda k: W(*cands[k])); a2, k2 = cands[best]; w = W(a2, k2)
print('N', N, 'best structured', best, 'W', w, 'C(N,3)', len(TRI), flush=True)
for st in range(steps):
    b2, l2 = a2.copy(), k2.copy()
    for _ in range(rng.choice([1, 1, 2, 3])):
        if rng.random() < 0.6:
            i, j = rng.sample(range(N), 2); v = rng.choice([-4, -2, -1, 0, 0, 1, 2, 4]); b2[i, j] = b2[j, i] = v
        else:
            l2[rng.randrange(N)] = rng.choice(range(-8, 9))
    w2 = W(b2, l2)
    if w2 >= w:
        if w2 > w: print('step', st, 'W', w2, flush=True)
        a2, k2, w = b2, l2, w2
print('final W', w); print(a2 / 2); print(k2 / 2)
