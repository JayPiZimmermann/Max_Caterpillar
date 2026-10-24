"""MEASURED: hill-climb for the largest f (3-localities seen / (n-3)!) of one general neuron,
integer weights c_uv, gam_v in [-W, W].  f values reported are EXACT for the reported instance.
Usage: python3 locf_climb.py n seconds W seed
"""
import sys, time, random, itertools, json
from locf import make_f

n, secs, W, seed = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rnd = random.Random(seed)
E = list(itertools.combinations(range(n), 2))


def star_seed():
    c0 = rnd.randrange(n)
    c = {}
    for v in range(n):
        if v != c0:
            c[tuple(sorted((c0, v)))] = rnd.choice([-1, 1])
    gam = [0] * n
    gam[c0] = -sum(c.values())
    return c, gam


def rand_seed():
    c = {e: rnd.choice([-W, W, -1, 1]) for e in E if rnd.random() < 0.3}
    gam = [rnd.choice([0, 0, 0, -1, 1]) for _ in range(n)]
    return c, gam


best = (0, None)
t0 = time.time()
while time.time() - t0 < secs:
    c, gam = star_seed() if rnd.random() < 0.3 else rand_seed()
    cur = make_f(n, c, gam)
    stale = 0
    while stale < 300 and time.time() - t0 < secs:
        c2, g2 = dict(c), list(gam)
        for _ in range(rnd.randint(1, 2)):
            if rnd.random() < 0.6:
                e = rnd.choice(E)
                v = rnd.randint(-W, W)
                if v: c2[e] = v
                else: c2.pop(e, None)
            else:
                g2[rnd.randrange(n)] = rnd.randint(-2 * W, 2 * W)
        val = make_f(n, c2, g2)
        if val >= cur:
            if val > cur: stale = 0
            else: stale += 1
            c, gam, cur = c2, g2, val
        else:
            stale += 1
    if cur > best[0]:
        best = (cur, (c, gam))
        print('n %d f %s (%.3f)  f/(n-1)(n-2) %.3f  c %s gam %s  %.0fs' % (
            n, cur, float(cur), float(cur) / ((n - 1) * (n - 2)), {'%d%d' % e: w for e, w in c.items()}, gam, time.time() - t0), flush=True)
print('FINAL n %d best f %s = %.4f' % (n, best[0], float(best[0])))
