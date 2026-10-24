"""r-tie localities with the arity (Moebius) quotient.

Locality L = (T, order), |T| = r: y_T tied at 0, outside coordinates
p_o = -B^{rank(o)} (rank 1 = highest).  Test functional: an r-fold mixed
difference prod_{t in T} D_{delta_t e_t} at z, which kills every function of
fewer than r of the z_T (so all auxiliary functions when r >= 3) and is nonzero
on max_r (germ of max_N).  A unit passes L iff its germ has a nonzero r-fold
mixed difference (tested exactly in integers on random z, delta; a "killed"
verdict is measured, not certified).

Covering bound: s_N >= #L / max_k passes(k).
Usage: python arity_ties.py N r [trials]
"""
import sys, itertools, random
from math import comb, factorial
sys.path.insert(0, 'scripts')
from vocabulary_search import dictionary, is_auxiliary, relu

N = int(sys.argv[1]); r = int(sys.argv[2])
trials = int(sys.argv[3]) if len(sys.argv) > 3 else 60
K0, _ = dictionary(N)
units = sorted(k for k in K0 if not is_auxiliary(k))
rng = random.Random(12345)
tests = []
for _ in range(trials):
    z = [rng.randint(-20, 20) for _ in range(r)]
    d = [rng.choice([-1, 1]) * rng.randint(1, 20) for _ in range(r)]
    tests.append((z, d))
subsets = [S for m in range(r + 1) for S in itertools.combinations(range(r), m)]

def arity_full(v, inner):
    def u(y):
        return relu(sum(v[i] * y[i] for i in range(r))
                    + sum(relu(y[i] - y[j]) for i, j in inner))
    for z, d in tests:
        tot = 0
        for S in subsets:
            y = list(z)
            for i in S:
                y[i] += d[i]
            tot += (-1) ** (r - len(S)) * u(y)
        if tot:
            return True
    return False

def passes(key, cache):
    h, M = key
    cnt = 0
    for T in itertools.combinations(range(N), r):
        Ts = set(T); idx = {t: n for n, t in enumerate(T)}
        rest = [o for o in range(N) if o not in Ts]
        inner = tuple((idx[i], idx[j]) for i, j in M if i in Ts and j in Ts)
        for order in itertools.permutations(rest):
            rank = {o: q + 1 for q, o in enumerate(order)}
            def above(i, j):  # is i above j at p
                if i in Ts: return j not in Ts
                if j in Ts: return False
                return rank[i] < rank[j]
            v = list(h)
            ok = True
            for (i, j) in M:
                if i in Ts and j in Ts:
                    continue
                if above(i, j):      # sigma(y_i - y_j) active: linear y_i - y_j
                    v[i] += 1; v[j] -= 1
            if any(v[o] for o in rest):
                continue
            vt = tuple(v[t] for t in T)
            ck = (vt, inner)
            if ck not in cache:
                cache[ck] = arity_full(vt, inner)
            if cache[ck]:
                cnt += 1
    return cnt

cache = {}
best = 0; arg = None; hist = {}
for k in units:
    c = passes(k, cache)
    hist[c] = hist.get(c, 0) + 1
    if c > best:
        best, arg = c, k
L = comb(N, r) * factorial(N - r)
print(f"N={N} r={r} units={len(units)} localities={L} maxpass={best} "
      f"bound={L/best:.4f} (N(N-1)(N-2)/12={N*(N-1)*(N-2)/12:.3f}) argmax={arg}")
print("pass histogram (top):", sorted(hist.items())[-6:])
