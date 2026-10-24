"""MEASURED: for Q-states (gamma == 0) of connected weighted graphs, the quantities
f_j(K) = sum_{|S|=j} Pr[random order of K\\S has zero in-weight at every vertex]
(no Lambda / (c) condition), j = 1, 2, 3, and f(K) (3-localities with (c), Lambda).
Hill-climb over integer weights in [-W, W] to estimate their maxima for connected K.
Usage: python3 qstate.py m seconds W seed
"""
import sys, time, random, itertools
from fractions import Fraction as Fr
from functools import lru_cache
from math import factorial
from locf import make_f

m, secs, W, seed = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rnd = random.Random(seed)
E = list(itertools.combinations(range(m), 2))


def fj(c, j):
    Wt = [[0] * m for _ in range(m)]
    for (u, v), w in c.items():
        Wt[u][v] = Wt[v][u] = w

    @lru_cache(maxsize=None)
    def cnt(X):  # number of valid bottom-up orders of the set X (all in-weights 0)
        if X == 0:
            return 1
        tot = 0
        for v in range(m):
            if X >> v & 1:
                Y = X & ~(1 << v)
                # v is the top of X: its in-weight = c(v, Y)
                if sum(Wt[v][u] for u in range(m) if Y >> u & 1) == 0:
                    tot += cnt(Y)
        return tot
    full = (1 << m) - 1
    s = Fr(0)
    for S in itertools.combinations(range(m), j):
        X = full
        for v in S:
            X &= ~(1 << v)
        s += Fr(cnt(X), factorial(m - j))
    return s


def connected(c):
    adj = {v: set() for v in range(m)}
    for (u, v), w in c.items():
        if w:
            adj[u].add(v); adj[v].add(u)
    seen, st = {0}, [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y); st.append(y)
    return len(seen) == m


best = {1: (0, None), 2: (0, None), 3: (0, None), 'f': (0, None)}
t0 = time.time()
while time.time() - t0 < secs:
    c = {e: rnd.choice([-1, 1, -W, W]) for e in E if rnd.random() < rnd.choice([0.2, 0.4, 0.7])}
    if not connected(c):
        continue
    for key in (1, 2, 3, 'f'):
        cur = make_f(m, c, [0] * m) if key == 'f' else fj(c, key)
        cc = dict(c)
        for it in range(150):
            c2 = dict(cc)
            e = rnd.choice(E)
            v = rnd.randint(-W, W)
            if v: c2[e] = v
            else: c2.pop(e, None)
            if not connected(c2):
                continue
            val = make_f(m, c2, [0] * m) if key == 'f' else fj(c2, key)
            if val >= cur:
                cc, cur = c2, val
        if cur > best[key][0]:
            best[key] = (cur, cc)
            print('m %d key %s new best %s (%.3f) c %s' % (m, key, cur, float(cur), {'%d%d' % e: w for e, w in cc.items()}), flush=True)
print('FINAL m', m, {k: float(v[0]) for k, v in best.items()})
