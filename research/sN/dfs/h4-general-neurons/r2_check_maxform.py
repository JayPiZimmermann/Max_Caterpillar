"""Independent EXACT spot check (Fractions) of the N=5 identity in max form
(does not share code with r2_certify.py; a sanity check, not a proof):
  max(a,b,c,d,e) = max(a,b) + relu(A) - relu(A+Q) + relu(u)/2 + relu(v)/2,
  A = max(d,e) - max(a,c),  Q = (max(a,b)+max(b,c)-max(b,d)-max(b,e))/2,
  u = max(b,c)+max(b,e)-max(a,b)-max(b,d),  v = max(b,c)+max(b,d)-max(a,b)-max(b,e).
Also checks that this max form equals the spec r2_spec_N5_k4.py pointwise."""
import random, itertools, runpy
from fractions import Fraction as Fr
r = lambda t: max(t, Fr(0))
def rhs(x):
    a, b, c, d, e = x; M = max
    A = M(d, e) - M(a, c); Q = (M(a, b) + M(b, c) - M(b, d) - M(b, e)) / 2
    u = M(b, c) + M(b, e) - M(a, b) - M(b, d); v = M(b, c) + M(b, d) - M(a, b) - M(b, e)
    return M(a, b) + r(A) - r(A + Q) + r(u) / 2 + r(v) / 2
s = runpy.run_path('r2_spec_N5_k4.py')
def spec(x):
    ev = lambda l, c: sum(Fr(li) * xi for li, xi in zip(l, x)) + sum(Fr(w) * r(x[i] - x[j]) for (i, j), w in c.items())
    return ev(*s['R']) + sum(Fr(d) * r(ev(l, c)) for d, l, c in s['NEURONS'])
rnd = random.Random(2026); bad = 0; n = 0
for trial in range(200000):
    k = rnd.choice([3, 4, 5, 7, 1000])  # small value sets force many ties
    x = [Fr(rnd.randint(-k, k), rnd.choice([1, 2, 3])) for _ in range(5)]
    n += 1
    if rhs(x) != max(x) or spec(x) != max(x): bad += 1
for x in itertools.product(range(-2, 3), repeat=5):  # full grid {-2..2}^5
    x = [Fr(t) for t in x]; n += 1
    if rhs(x) != max(x) or spec(x) != max(x): bad += 1
print('points', n, 'mismatches', bad)
