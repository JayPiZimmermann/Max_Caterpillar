"""Round 3.  EXACT: given a support of atoms max(sum m_P, sum m_Q) (from r3_lp.py npz),
solve for rational coefficients on random integer points (exact sympy solve), then
certify the identity max_N = R + sum d_k max(A_k, B_k) on all of R^N with
r2_certify.certify (braid cells x sign vectors, exact Fourier-Motzkin).
Usage: python r3_cert.py file.npz
"""
import sys, itertools, random
from fractions import Fraction as Fr
import numpy as np
import sympy
from r2_certify import certify

z = np.load(sys.argv[1])
syms = [tuple(s) for s in z['syms']]
atoms = z['atoms']
N = max(max(s) for s in syms) + 1
deg = atoms.shape[1] // 2
pairs = list(itertools.combinations(range(N), 2))


def side_la(idx):
    """<l,x> + sum a_ij relu(x_i - x_j) for sum of m_s."""
    l = [Fr(0)] * N; a = {}
    for k in idx:
        i, j = syms[k]
        l[j] += 1
        if i != j:
            a[(i, j)] = a.get((i, j), 0) + 1
    return l, a


def ev(l, a, x):
    return sum(l[i] * x[i] for i in range(N)) + sum(c * max(x[i] - x[j], 0) for (i, j), c in a.items())


K = len(atoms)
neur = []
for row in atoms:
    lA, aA = side_la(row[:deg]); lB, aB = side_la(row[deg:])
    l = [p - q for p, q in zip(lA, lB)]
    a = dict(aA)
    for p, c in aB.items():
        a[p] = a.get(p, 0) - c
    neur.append((l, a, lB, aB))
rnd = random.Random(1)
nunk = K + N + len(pairs)
rows, rhs = [], []
for _ in range(nunk + 40):
    x = [rnd.randint(-10**6, 10**6) for _ in range(N)]
    r = []
    for l, a, lB, aB in neur:
        r.append(max(ev(l, a, x), 0) + ev(lB, aB, x))
    r += x + [max(x[i] - x[j], 0) for i, j in pairs]
    rows.append(r); rhs.append(max(x))
Msym = sympy.Matrix(rows); bsym = sympy.Matrix(rhs)
sol, params = Msym.gauss_jordan_solve(bsym)
sol = sol.subs({p: 0 for p in params})
d = [Fr(str(sympy.nsimplify(v))) for v in sol[:K]]
p = [Fr(str(v)) for v in sol[K:K + N]]
s = [Fr(str(v)) for v in sol[K + N:]]
print('free params', len(params), 'coefficients d', [str(v) for v in d])
# assemble spec
Rl = list(p); Ra = {pr: s[t] for t, pr in enumerate(pairs) if s[t] != 0}
NEUR = []
for dk, (l, a, lB, aB) in zip(d, neur):
    if dk == 0:
        continue
    for i in range(N):
        Rl[i] += dk * lB[i]
    for pr, c in aB.items():
        Ra[pr] = Ra.get(pr, 0) + dk * c
    NEUR.append((dk, l, a))
print('nonzero neurons', len(NEUR))
nreg, fails = certify(N, (Rl, Ra), NEUR)
print('CERTIFIED' if not fails else 'NOT an identity', 'N', N, 'neurons', len(NEUR))
