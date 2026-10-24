# Independent check of the peeling recursion and of the bound
#   f(H,Gam) := W(H,Gam)/(n-3)! <= (3/2)(n-2)
# for random weighted graphs with RATIONAL (non-integer) weights, using
# exact Fractions and direct definitions (no closed forms except the Lambda
# corner sum, recomputed from the germ).
#   W(H,Gam) = #{(T, order of O) : up-weight(o)=Gam_o for o in O,
#              sum_T Gam = c(E(T)), Lambda != 0}
# Gam is chosen so that many localities pass: Gam_o := up-weight in a random
# reference locality, Gam_T solved from (c) with random split.
import itertools, random
from fractions import Fraction as Fr
from math import factorial
def W(V, c, Gam):
    cnt = 0
    for T in itertools.combinations(V, 3):
        O = [v for v in V if v not in T]
        cET = sum(c.get(frozenset(e), 0) for e in itertools.combinations(T, 2))
        if sum(Gam[t] for t in T) != cET: continue
        d = {t: sum(c.get(frozenset((t, u)), 0) for u in T if u != t) for t in T}
        lam = 0
        for r in range(4):
            for S in itertools.combinations(T, r):
                # G(1_S) = sum_{t in S} v_t + sum_{e in T, e meets S} c_e,  v_t = Gam_t - d_t
                val = sum(Gam[t] - d[t] for t in S) + sum(c.get(frozenset(e), 0) for e in itertools.combinations(T, 2) if set(e) & set(S))
                lam += (-1)**(3 - r) * max(val, 0)
        if lam == 0: continue
        for ordO in itertools.permutations(O):
            ok = True
            for i, o in enumerate(ordO):
                up = sum(c.get(frozenset((o, u)), 0) for u in list(T) + list(ordO[:i]))
                if up != Gam[o]: ok = False; break
            if ok: cnt += 1
    return cnt
def deg(V, c, x): return sum(c.get(frozenset((x, u)), 0) for u in V if u != x)
random.seed(5)
worst = {}
for trial in range(400):
    n = random.choice([4, 5, 6])
    V = list(range(n))
    c = {}
    dens = random.random()
    for e in itertools.combinations(V, 2):
        if random.random() < dens: c[frozenset(e)] = Fr(random.randint(1, 3), random.randint(1, 2))
    # reference locality
    perm = V[:]; random.shuffle(perm)
    T, O = perm[:3], perm[3:]
    Gam = {}
    for i, o in enumerate(O):
        Gam[o] = sum(c.get(frozenset((o, u)), 0) for u in T + O[:i])
    cET = sum(c.get(frozenset(e), 0) for e in itertools.combinations(T, 2))
    a = Fr(random.randint(-4, 4), random.randint(1, 2)); b = Fr(random.randint(-4, 4), random.randint(1, 2))
    Gam[T[0]], Gam[T[1]], Gam[T[2]] = a, b, cET - a - b
    w = W(V, c, Gam)
    R = [x for x in V if Gam[x] == deg(V, c, x)]
    rec = sum(W([v for v in V if v != x], c, Gam) for x in R) if n > 3 else None
    assert rec == w, (n, c, Gam, w, rec)
    f = Fr(w, factorial(n - 3))
    worst[n] = max(worst.get(n, 0), f)
    assert f <= Fr(3, 2) * (n - 2), (n, c, Gam, f)
print("recursion identity and bound hold on 400 random rational instances; max f per n:", {k: str(v) for k, v in worst.items()})
