#!/usr/bin/env python3
"""s'_k: minimum number of local units whose combination equals max_k modulo
sums of functions each independent of one coordinate.

Constraint rows: k-fold mixed differences D f(b, h) on sampled integer boxes,
plus the base box (0, 1).  Fewer rows = a relaxation, so 'no combination of
size s satisfies the sampled rows' (exact rational elimination) is a rigorous
proof that s'_k > s for the given vocabulary.  Vocabulary = S_k-orbits of the
classes in data/lvocab_N_k.pkl.
Usage: python3 sprime.py N k smax
"""
import itertools, pickle, random, sys
from fractions import Fraction
N, k, smax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
voc = pickle.load(open(f'/home/jzimmermann/code/Max_Caterpillar/research/sN/ktie/data/lvocab_{N}_{k}.pkl', 'rb'))
def relu(t): return t if t > 0 else 0
funcs = set()
for v, M in voc:
    for perm in itertools.permutations(range(k)):
        vv = [0] * k
        for a in range(k): vv[perm[a]] = v[a]
        mm = []
        for i, j in M:
            a, b = perm[i], perm[j]
            if a > b: vv[a] += 1; vv[b] -= 1; a, b = b, a
            mm.append((a, b))
        funcs.add((tuple(vv), tuple(sorted(mm))))
funcs = sorted(funcs)
rng = random.Random(3)
boxes = [((0,) * k, (1,) * k)] + [(tuple(rng.randint(-5, 5) for _ in range(k)), tuple(rng.randint(1, 5) for _ in range(k))) for _ in range(60 * k)]
def D(f, b, hh):
    tot = 0
    for bits in range(1 << k):
        x = [b[i] + (hh[i] if bits >> i & 1 else 0) for i in range(k)]
        tot += (-1) ** (k - bin(bits).count('1')) * f(x)
    return tot
def ev(key):
    v, M = key
    return lambda x: relu(sum(a * c for a, c in zip(v, x)) + sum(relu(x[i] - x[j]) for i, j in M))
cols = [tuple(D(ev(g), b, hh) for b, hh in boxes) for g in funcs]
target = tuple(D(max, b, hh) for b, hh in boxes)
print(f'N={N} k={k}: {len(funcs)} local units (orbit closure), {len(boxes)} boxes')
# dedupe columns up to scaling, drop zero columns
def normal(c):
    nz = next((x for x in c if x), None)
    if nz is None: return None
    return tuple(Fraction(x, nz) for x in c)
uniq = {}
for g, c in zip(funcs, cols):
    n = normal(c)
    if n is not None: uniq.setdefault(n, g)
reps = list(uniq.items())
print('  distinct nonzero D-columns up to scale:', len(reps))
def solvable(cs, sub=None):
    # exact: is target in span(cs)?  (on the rows `sub` first: infeasible there => infeasible)
    if sub is None:
        if not solvable(cs, list(range(0, len(target), max(1, len(target) // 25)))): return False
        sub = range(len(target))
    m = len(cs); rows = [[c[i] for c in cs] + [target[i]] for i in sub]
    A = [[Fraction(x) for x in r] for r in rows]
    piv = 0
    for c in range(m + 1):
        p = next((i for i in range(piv, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        if c == m: return False
        A[piv], A[p] = A[p], A[piv]
        for i in range(len(A)):
            if i != piv and A[i][c] != 0:
                f = A[i][c] / A[piv][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[piv])]
        piv += 1
    return True
for s in range(1, smax + 1):
    found = None
    for combo in itertools.combinations(range(len(reps)), s):
        cs = [reps[i][0] for i in combo]
        # quick check on base box: some column nonzero there is required
        if all(c[0] == 0 for c in cs): continue
        if solvable(cs):
            found = [reps[i][1] for i in combo]; break
    print(f'  size {s}:', 'FEASIBLE on samples' if found else 'infeasible (rigorous)', found or '', flush=True)
    if found: break
