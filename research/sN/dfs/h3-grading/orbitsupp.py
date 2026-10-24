"""Orbit-support lower bound.  If max_N = sum_{k in K} d_k U_k + R (R in A_N), averaging over S_N gives
max_N in span{O_o : o meets K} + A_N^{S_N}, O_o = orbit sum of the key orbit o.  Hence
s_N >= o_N := min #{orbits} whose orbit sums together with A_N^{S_N} span max_N.
This script: exact (mod p) rank data and exhaustive search over orbit subsets of increasing size
(feasibility of a subset S: rank(A^S + O_S + max) == rank(A^S + O_S)).  Mod-p ranks of exact integer
evaluations at random points (measured; rank deficiency mod p only makes subsets look feasible
falsely if max's residual vanishes mod p, controlled by a second prime-free check with a 2nd seed).
Usage: orbitsupp.py N [maxsize]"""
import sys, itertools, time, json
import numpy as np
from common import keys
from sym import act_key, orbits, young_gens, eval_keys
P = 2147483647
N = int(sys.argv[1]); maxsize = int(sys.argv[2]) if len(sys.argv) > 2 else 6
ks = keys(N)
orbs = [o for o, _ in orbits(ks, act_key, young_gens(N, (N,)))]
def rank(A):
    A = np.array(A, dtype=np.int64) % P; r = 0
    rows, cols = A.shape
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i, c]), None)
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]; A[r] = (A[r] * pow(int(A[r, c]), P - 2, P)) % P
        for i in np.nonzero(A[:, c])[0]:
            if i != r: A[i] = (A[i] - A[i, c] * A[r]) % P
        r += 1
        if r == rows: break
    return r
def run(seed):
    rng = np.random.default_rng(seed)
    npts = len(orbs) + 30
    X = rng.integers(-10**5, 10**5, size=(npts, N), endpoint=True).astype(np.int64)
    pos = np.maximum(X, 0).sum(1); neg = np.maximum(-X, 0).sum(1)
    pair = sum(np.maximum(X[:, i] - X[:, j], 0) for i in range(N) for j in range(N) if i != j)
    Arows = [pos, neg, pair, X.sum(1)]
    kidx = {k: n for n, k in enumerate(ks)}
    EK = eval_keys(ks, X)
    O = [sum(EK[kidx[k]] for k in o) for o in orbs]
    mx = X.max(1)
    return Arows, O, mx
Arows, O, mx = run(1)
Arows2, O2, mx2 = run(2)
rA = rank(Arows); rAll = rank(Arows + O); rmx = rank(Arows + O + [mx])
grades = [len(next(iter(o))[1]) for o in orbs]
print(json.dumps({'N': N, 'orbits': len(orbs), 'rank_A_sym': rA, 'rank_V_sym': rAll, 'max_in_V': rmx == rAll,
                  'orbits_by_grade': {g: grades.count(g) for g in sorted(set(grades))}}), flush=True)
t0 = time.time()
found = None
for s in range(1, maxsize + 1):
    cnt = 0
    for S in itertools.combinations(range(len(orbs)), s):
        if N >= 4 and not any(grades[i] == N - 2 for i in S):   # max_N is grade N-2 mod lower grades
            continue
        B = Arows + [O[i] for i in S]
        r = rank(B)
        if rank(B + [mx]) == r:
            B2 = Arows2 + [O2[i] for i in S]
            if rank(B2 + [mx2]) == rank(B2):
                cnt += 1
                if found is None: found = S
    print(json.dumps({'size': s, 'feasible_subsets': cnt, 'example': found, 'secs': round(time.time() - t0, 1)}), flush=True)
    if cnt: break
