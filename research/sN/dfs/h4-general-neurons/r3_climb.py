"""Round 3.  MEASURED search for general neurons passing MANY 3-localities (exact counts,
heuristic search).  Integer weights lam_ij, l_v in [-W, W], l_0 fixed by translation
invariance.  Hill climbing with random single-weight moves and restarts from sparse /
star seeds.  Every reported count is exact for the reported neuron (a certified witness
that max passing >= count); the maximum itself is only a measured lower estimate.
Usage: python r3_climb.py N seconds [W] [seed]
"""
import sys, time, random, math, itertools, json
from r3_pass import count, star

N = int(sys.argv[1]); secs = float(sys.argv[2])
W = int(sys.argv[3]) if len(sys.argv) > 3 else 2
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
rnd = random.Random(seed)
pairs = list(itertools.combinations(range(N), 2))
allL = math.comb(N, 3) * math.factorial(N - 3)


def fix(l, lam):
    l = list(l)
    l[0] = -(sum(l[1:]) + sum(lam.values()))
    return l, {p: v for p, v in lam.items() if v}


def seed_state():
    r = rnd.random()
    if r < 0.3:
        w = [rnd.choice([-1, 1, -2, 2]) for _ in range(N)]
        return star(N, rnd.randrange(N), w)
    lam = {}
    for p in pairs:
        if rnd.random() < 0.3:
            lam[p] = rnd.choice([-2, -1, 1, 2])
    l = [0] * N
    for v in range(1, N):
        if rnd.random() < 0.2:
            l[v] = rnd.choice([-2, -1, 1, 2])
    return fix(l, lam)


best = (-1, None)
t0 = time.time()
while time.time() - t0 < secs:
    l, lam = seed_state()
    cur = count(N, l, lam)
    stall = 0
    while stall < 60 and time.time() - t0 < secs:
        l2, lam2 = list(l), dict(lam)
        if rnd.random() < 0.75:
            p = rnd.choice(pairs)
            lam2[p] = rnd.randint(-W, W)
        else:
            l2[rnd.randrange(1, N)] = rnd.randint(-W, W)
        l2, lam2 = fix(l2, lam2)
        c = count(N, l2, lam2)
        if c >= cur:
            if c > cur:
                stall = 0
            else:
                stall += 1
            l, lam, cur = l2, lam2, c
        else:
            stall += 1
    if cur > best[0]:
        best = (cur, (l, lam))
        print('N', N, 'best', cur, 'of', allL, 'frac %.3f' % (cur / allL), 'l', l,
              'lam', {'%d%d' % p: v for p, v in lam.items()}, '%.0fs' % (time.time() - t0), flush=True)
print('FINAL N', N, 'max found', best[0], 'of', allL, 'frac %.4f' % (best[0] / allL))
json.dump({'N': N, 'count': best[0], 'all': allL, 'l': best[1][0],
           'lam': {'%d,%d' % p: v for p, v in best[1][1].items()}},
          open('r3_climb_N%d_s%d.json' % (N, seed), 'w'))
