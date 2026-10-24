"""EXACT checks of the lemmas used in PROOFS.md, Theorem L (k(N) >= sqrt(N)/2), on random
instances (weights in {-2..2}, Fractions):
 (1) peeling recursion == brute force (done in locf.py self-test, repeated here);
 (2) Q-state with isolated vertices: f(X) == f(X minus isolated);
 (3) f <= B(n) with B(3)=1, B(4)=4, B(m)=max((m-1)/(m-3) B(m-1), m(m-2)/((m-3)(m-4)) B(m-2));
 (4) B(m) <= (m-1)(m-2) sqrt(m)/3 for 3 <= m <= 2000.
Usage: python3 check_lemmas.py trials seed
"""
import sys, random, itertools, math
from fractions import Fraction as Fr
from locf import make_f, brute

trials, seed = int(sys.argv[1]), int(sys.argv[2])
rnd = random.Random(seed)
B = {3: Fr(1), 4: Fr(4)}
for m in range(5, 2001):
    B[m] = max(Fr(m - 1, m - 3) * B[m - 1], Fr(m * (m - 2), (m - 3) * (m - 4)) * B[m - 2])
for m in range(3, 2001):
    # (m-1)(m-2) sqrt(m)/3 >= B  <=>  ((m-1)(m-2))^2 m >= 9 B^2   (exact)
    assert ((m - 1) * (m - 2)) ** 2 * m >= 9 * B[m] ** 2, m
print('(4) ok up to 2000')
n1 = n2 = n3 = 0
for t in range(trials):
    n = rnd.randint(4, 7)
    c = {e: rnd.choice([-2, -1, 1, 2]) for e in itertools.combinations(range(n), 2) if rnd.random() < 0.45}
    gam = [rnd.choice([0, 0, 0, -1, 1, 2, -2]) for _ in range(n)]
    f = make_f(n, c, gam)
    assert f == brute(n, c, gam); n1 += 1
    assert f <= B[n]; n3 += 1
    # Q-state with isolated vertices appended
    k = rnd.randint(1, 3)
    cq = dict(c)
    fq = make_f(n, cq, [0] * n)
    fiso = make_f(n + k, cq, [0] * (n + k))
    assert fq == fiso, (c, fq, fiso); n2 += 1
print('(1) peeling==brute', n1, '(2) isolated', n2, '(3) f<=B', n3, 'all ok')
