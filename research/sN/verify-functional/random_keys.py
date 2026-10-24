#!/usr/bin/env python3
"""Steps 1-4 do not use caterpillar structure: test Lambda U != 0 => [A(p)=0 and
M(T) nonempty] (which implies Pass) and the digit equivalence on random keys
with arbitrary integer heads (large coefficients, sum not forced to 0) and
arbitrary pair sets M (pairs i<j), with per-key stated B, C.
Usage: python3 random_keys.py N trials seed hmax
"""
import itertools, random, sys
from fractions import Fraction as F
N, trials, seed, hmax = map(int, sys.argv[1:5])
rng = random.Random(seed)
relu = lambda t: t if t > 0 else 0
pairs = list(itertools.combinations(range(N), 2))
def A(k, y):
    h, M = k
    return sum(a * b for a, b in zip(h, y)) + sum(relu(y[i] - y[j]) for i, j in M)
fail = dict(strong=0, digit=0); nz = 0; azero = 0; tested = 0
for _ in range(trials):
    # bias toward A(p)=0 cases: small heads half the time
    hm = rng.choice([1, 2, hmax])
    h = [rng.randint(-hm, hm) for _ in range(N)]
    M = [e for e in pairs if rng.random() < 0.4]
    k = (h, M)
    B = 2 * max(abs(x) + N for x in h) + 1
    C = 1 + max(sum(abs(h[t]) for t in T) for T in itertools.combinations(range(N), 3)) + 2 * N
    eps = F(1, 8 * C); dl = eps / 2
    for T in itertools.combinations(range(N), 3):
        out = [o for o in range(N) if o not in T]
        for perm in itertools.permutations(range(1, N - 2)):
            rho = dict(zip(out, perm)); tested += 1
            p = [F(0) if o in T else F(-B ** rho[o]) for o in range(N)]
            a, b = T[0], T[1]; val = 0
            for sg in (1, -1):
                for s, w in ((1, 1), (-1, 1), (0, -2)):
                    z = list(p); z[a] += sg * eps + s * dl; z[b] += sg * eps - s * dl
                    val += sg * w * relu(A(k, z))
            Ap = A(k, p); azero += Ap == 0
            c = []
            for o in out:
                kap = h[o] + sum(1 for i, j in M if i == o)
                nb = [j if i == o else i for i, j in M if o in (i, j)]
                c.append(kap - sum(1 for u in nb if u in T or rho[u] < rho[o]))
            if (Ap == 0) != all(x == 0 for x in c): fail['digit'] += 1
            if val:
                nz += 1
                if not (Ap == 0 and any(i in T and j in T for i, j in M)): fail['strong'] += 1
print(f'N={N} trials={trials} seed={seed} hmax={hmax} (key,locality) pairs={tested} '
      f'A(p)=0: {azero} Lambda!=0: {nz} fails: {fail}')
