"""Sanity checks for research/sN/simplify/exponential.md.

(1) Rooted-star faces (each leaf omitted / linear / hinge): the exact mixed difference
    Delta_rho U is nonzero only if the unit passes rho ((a) and (s)); N = 4, 5.
(2) Random descriptions of the caterpillar shape (spine paths + pendants with kappa = 0,
    arbitrary integer heads otherwise): #passed permutations <= 6^m m! (N-m)!  and
    <= 5^m m! (N-m)!  (the base-5 remark), N <= 7.
(3) Block inequalities at y = 1/6 and y = 1/5.
"""
import itertools, random, sys
from fractions import Fraction as F
from math import factorial

relu = lambda t: t if t > 0 else 0

def arg(h, M, y):
    return sum(h[o] * y[o] for o in range(len(y))) + sum(relu(y[i] - y[j]) for i, j in M)

def kappa(h, M, o):
    return h[o] + sum(1 for i, j in M if i == o)

def adj(M, N):
    A = [set() for _ in range(N)]
    for i, j in M:
        A[i].add(j); A[j].add(i)
    return A

def passes(h, M, A, rho, m):
    N = len(h); pos = rho
    T = {o for o in range(N) if pos[o] < m}
    for o in range(N):
        if o not in T:
            up = sum(1 for x in A[o] if pos[x] < pos[o])
            if up != kappa(h, M, o):
                return False
    for t in T:
        if not (A[t] & T) and kappa(h, M, t) == 0:
            return False
    return True

def mixed(h, M, rho, m, B, d):
    N = len(h)
    T = [o for o in range(N) if rho[o] < m]
    p = [F(0) if rho[o] < m else F(-(B ** rho[o])) for o in range(N)]
    tot = F(0)
    for r in range(m + 1):
        for S in itertools.combinations(T, r):
            y = list(p)
            for s in S:
                y[s] += d
            tot += (-1) ** (m - r) * relu(arg(h, M, y))
    return tot

def star_faces(N):
    for a in range(N):
        for c in range(N):
            if c == a:
                continue
            leaves = [l for l in range(N) if l not in (a, c)]
            for st in itertools.product(range(3), repeat=len(leaves)):
                h = [0] * N; h[c] += 1; h[a] -= 1; M = []
                for l, s in zip(leaves, st):
                    if s == 1:
                        h[c] += 1; h[l] -= 1
                    elif s == 2:  # relu(y_c - y_l), normalised to i<j
                        if c < l:
                            M.append((c, l))
                        else:  # relu(y_c-y_l) = relu(y_l-y_c) + y_c - y_l
                            M.append((l, c)); h[c] += 1; h[l] -= 1
                yield h, M

def check1(N):
    bad = 0; tot = 0
    for h, M in star_faces(N):
        A = adj(M, N)
        C = sum(abs(x) for x in h) + 2 * len(M)
        d = F(1, C + 1); B = C + 1
        for m in range(3, N + 1):
            for rho in itertools.permutations(range(N)):
                v = mixed(h, M, rho, m, B, d)
                if v != 0:
                    tot += 1
                    if not passes(h, M, A, rho, m):
                        bad += 1
    print(f"(1) N={N}: nonzero mixed differences {tot}, without pass {bad}")
    return bad == 0

def random_shape(N, rng):
    verts = list(range(N)); rng.shuffle(verts)
    h = [rng.randint(-2, 3) for _ in range(N)]
    M = []; i = 0; pend = []
    while i < N:
        L = rng.randint(1, 4)
        spine = verts[i:i + L]; i += L
        for u, v in zip(spine, spine[1:]):
            M.append((min(u, v), max(u, v)))
        for s in spine:
            for _ in range(rng.randint(0, 2)):
                if i < N:
                    u = verts[i]; i += 1
                    M.append((min(s, u), max(s, u))); pend.append(u)
    # pendants: kappa = 0
    for u in pend:
        h[u] = -sum(1 for a, b in M if a == u)
    return h, M

def check2(N, trials, rng):
    worst6 = worst5 = 0.0
    for _ in range(trials):
        h, M = random_shape(N, rng)
        A = adj(M, N)
        for m in range(3, N + 1):
            cnt = sum(1 for rho in itertools.permutations(range(N)) if passes(h, M, A, rho, m))
            base = factorial(m) * factorial(N - m)
            worst6 = max(worst6, cnt / (base * 6 ** m))
            worst5 = max(worst5, cnt / (base * 5 ** m))
    print(f"(2) N={N}: max passes/(6^m m!(N-m)!) = {worst6:.4f}, /(5^m ...) = {worst5:.4f}")
    return worst5 <= 1

def check3():
    for y in (F(1, 6), F(1, 5)):
        pair = F(1, 2) + 2 * y + y * y
        triple_match = F(1, 2) + 2 * y + 3 * y * y + y ** 3
        triple_exact = F(1, 3) + 2 * y + 3 * y * y + y ** 3
        single = F(1, 2) + y
        print(f"(3) y={y}: pair {pair}, triple(match) {triple_match}, triple(1/3) {triple_exact}, single {single}")

if __name__ == "__main__":
    rng = random.Random(1)
    ok = check1(4) and check1(5)
    for N in (5, 6, 7):
        ok = check2(N, 40 if N < 7 else 12, rng) and ok
    check3()
    print("OK" if ok else "FAIL")

def adversarial(N, trials, rng):
    """Heads tuned so that the unit passes a random locality (rho0, m0)."""
    worst = {}
    done = 0
    while done < trials:
        h, M = random_shape(N, rng)
        A = adj(M, N)
        pend = {u for u in range(N) if len(A[u]) == 1 and kappa(h, M, u) == 0}
        m0 = rng.randint(3, N)
        rho0 = list(range(N)); rng.shuffle(rho0)
        ok = True
        for o in range(N):
            if rho0[o] >= m0:
                up = sum(1 for x in A[o] if rho0[x] < rho0[o])
                need = up - sum(1 for i, j in M if i == o)
                if o in pend and up != 0:
                    ok = False
                h[o] = need
            elif o not in pend:
                h[o] = rng.randint(-1, 2)
        if not ok or not passes(h, M, A, rho0, m0):
            continue
        done += 1
        for m in range(3, N + 1):
            cnt = sum(1 for rho in itertools.permutations(range(N)) if passes(h, M, A, rho, m))
            r = cnt / (factorial(m) * factorial(N - m))
            worst[m] = max(worst.get(m, 0), r)
    print(f"(4) N={N}: max passes/(m!(N-m)!) by m: " +
          ", ".join(f"m={m}: {v:.3f} (5^m={5**m})" for m, v in sorted(worst.items())))

if __name__ == "__main__":
    for N in (6, 7):
        adversarial(N, 150 if N == 6 else 40, random.Random(N))
