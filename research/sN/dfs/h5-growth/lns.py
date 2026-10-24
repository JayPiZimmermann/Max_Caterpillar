"""Large-neighbourhood search for small supports (heuristic upper bounds).
State: an exact solution K (pickle with 'K' keys).  Each round restricts the
big-M MILP to a pool = K + a random set of units sharing kink groups with K
+ random extra units, and solves to optimality within a time limit.
Every improvement is re-solved exactly over Q (solve.System.solve).
usage: python lns.py N mode start.pkl rounds pool_extra time_per_round seed out.pkl
"""
import pickle
import sys
import time

import highspy
import numpy as np

from solve import System, prune

N, MODE, START, ROUNDS, EXTRA, TPR, SEED, OUT = (int(sys.argv[1]), sys.argv[2], sys.argv[3],
                                                 int(sys.argv[4]), int(sys.argv[5]),
                                                 float(sys.argv[6]), int(sys.argv[7]), sys.argv[8])
S = System(N)
SR = [S.Dm.shape[0] - 1] if MODE == 'top' else list(range(S.Dm.shape[0]))
idx = {k: i for i, k in enumerate(S.U)}
K = [idx[k] for k in pickle.load(open(START, 'rb'))['K']]
rng = np.random.default_rng(SEED)
BM = 4.0


def milp(pool, start, tl):
    pool = list(pool)
    m = len(pool)
    pos = {u: i for i, u in enumerate(pool)}
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('time_limit', tl)
    h.setOptionValue('threads', 2)
    h.setOptionValue('random_seed', int(rng.integers(1 << 30)))
    inf = highspy.kHighsInf
    for _ in range(m):
        h.addVar(-BM, BM)
    for _ in range(m):
        h.addVar(0, 1)
    h.changeColsIntegrality(m, np.arange(m, 2 * m, dtype=np.int32),
                            np.array([highspy.HighsVarType.kInteger] * m))
    h.changeColsCost(m, np.arange(m, 2 * m, dtype=np.int32), np.ones(m))
    gis = sorted({gi for u in pool for gi, _ in S.ug[u]})
    for gi in gis:
        grp = S.groups[S.gkeys[gi]]
        it = [(pos[u], lam) for u, lam in grp.items() if u in pos]
        h.addRow(0, 0, len(it), np.array([a for a, _ in it], dtype=np.int32),
                 np.array([float(b) for _, b in it]))
    for s in SR:
        it = [(pos[u], float(S.Dm[s, u])) for u in pool if S.Dm[s, u]]
        t = float(S.tD[s])
        h.addRow(t, t, len(it), np.array([a for a, _ in it], dtype=np.int32),
                 np.array([b for _, b in it]))
    for i in range(m):
        h.addRow(-inf, 0, 2, np.array([i, m + i], dtype=np.int32), np.array([1.0, -BM]))
        h.addRow(-inf, 0, 2, np.array([i, m + i], dtype=np.int32), np.array([-1.0, -BM]))
    if start is not None:
        sol = highspy.HighsSolution()
        x = [0.0] * (2 * m)
        for u, v in start.items():
            x[pos[u]] = float(v)
            x[m + pos[u]] = 1.0
        sol.col_value = x
        sol.value_valid = True
        h.setSolution(sol)
    h.run()
    try:
        x = h.getSolution().col_value
    except Exception:
        return None
    if not x or len(x) < 2 * m:
        return None
    return [pool[i] for i in range(m) if x[m + i] > 0.5 and abs(x[i]) > 1e-9]


cur = S.solve(K, SR)
assert cur is not None
K = [u for u in K if cur.get(u, 0) != 0]
print('start', len(K), flush=True)
t0 = time.time()
for r in range(ROUNDS):
    nb = sorted({v for u in K for gi, _ in S.ug[u] for v in S.groups[S.gkeys[gi]]} - set(K))
    take = rng.choice(nb, size=min(EXTRA, len(nb)), replace=False).tolist() if nb else []
    rnd = rng.choice(S.n, size=EXTRA // 3, replace=False).tolist()
    # drop a random fraction of K from the pool to force moves
    keep = [u for u in K if rng.random() > 0.0]
    pool = sorted(set(keep) | set(take) | set(rnd))
    start = {u: cur[u] for u in K} if all(abs(float(cur[u])) <= BM for u in K) else None
    K2 = milp(pool, start, TPR)
    if K2 and len(K2) < len(K):
        res = prune(S, K2, SR)
        if res and len(res[0]) < len(K):
            K, cur = res
            pickle.dump({'N': N, 'mode': MODE, 'K': [S.U[u] for u in K],
                         'd': {S.U[u]: cur[u] for u in K}}, open(OUT, 'wb'))
    print(f'round {r}: pool {len(pool)} found {len(K2) if K2 else None} best {len(K)} t={time.time()-t0:.0f}s', flush=True)
