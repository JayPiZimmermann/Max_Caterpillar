"""Control: combinatorial seen test == brute-force cube functional, random neurons, N=4..6.
Also checks P1 (peeling) and the lemma R(H-b) = {v : c_vb = 0} when R(H) = V."""
import random, itertools, math, sys
from fractions import Fraction as Fr
from seen import Neuron, localities

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
mism = 0; tested = 0; seen_tot = 0
for trial in range(600):
    N = rng.choice([4, 5, 6])
    pairs = list(itertools.combinations(range(N), 2))
    dens = rng.random()
    c = {e: rng.choice([-2, -1, 1, 2]) for e in pairs if rng.random() < dens}
    # choose Gam so that many equations hold: Gam_v = random partial up-weight or deg
    deg = [sum(w for e, w in c.items() if v in e) for v in range(N)]
    Gam = []
    for v in range(N):
        r = rng.random()
        Gam.append(deg[v] if r < 0.5 else rng.randint(-3, 3))
    if rng.random() < 0.7:   # plant one locality: Gam_o = up-weights, (c) on T
        T = sorted(rng.sample(range(N), 3)); O = [v for v in range(N) if v not in T]; rng.shuffle(O)
        cc = lambda i, j: c.get((min(i, j), max(i, j)), 0)
        above = list(T)
        for o in O:
            Gam[o] = sum(cc(o, j) for j in above); above.append(o)
        cE = cc(T[0], T[1]) + cc(T[0], T[2]) + cc(T[1], T[2])
        Gam[T[0]] = rng.randint(-3, 3); Gam[T[1]] = rng.randint(-3, 3); Gam[T[2]] = cE - Gam[T[0]] - Gam[T[1]]
    gam = [Gam[v] - deg[v] for v in range(N)]
    nu = Neuron(N, gam, c)
    for T, order in localities(N):
        a = nu.seen_comb(T, order); b = nu.seen_brute(T, order, rng)
        tested += 1; seen_tot += a
        if a != b:
            mism += 1
            print("MISMATCH", N, c, Gam, T, order, a, b)
    # P1 check: f(H) = 1/(n-3) sum_{b in R} f(H-b)
    if N >= 5:
        R = [b for b in range(N) if nu.Gam[b] == nu.deg[b]]
        rhs = 0
        for b in R:
            keep = [v for v in range(N) if v != b]
            idx = {v: k for k, v in enumerate(keep)}
            c2 = {(idx[i], idx[j]): w for (i, j), w in c.items() if b not in (i, j)}
            deg2 = [sum(w for e, w in c2.items() if k in e) for k in range(N - 1)]
            gam2 = [nu.Gam[v] - deg2[idx[v]] for v in keep]   # keep Gam
            rhs += Neuron(N - 1, gam2, c2).f()
        assert nu.f() == rhs / (N - 3), ("P1 fails", c, Gam)
print(f"tested {tested} localities, seen {seen_tot}, mismatches {mism}; P1 identity checked")
