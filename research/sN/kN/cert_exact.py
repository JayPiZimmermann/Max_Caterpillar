"""EXACT: from a support of neurons (chainlp.py json), solve the linear system (Boolean identity +
chain-class equations) in rationals, then certify the real identity max_N = R + sum d relu(G) on
all of R^N with the independent cell certifier ../dfs/h4-general-neurons/r2_certify.py
(Fourier-Motzkin over braid cells x sign vectors), and write the scripts/smalln JSON format.
Usage: python3 cert_exact.py sup.json Name out.json
"""
import sys, json, itertools, importlib.util, os
from fractions import Fraction as Fr

sup = json.load(open(sys.argv[1]))
N = sup['N']
pairs = list(itertools.combinations(range(N), 2))
NS = 1 << N


def setfun(gor):
    out = []
    for S in range(NS):
        b = [(S >> i) & 1 for i in range(N)]
        v = sum(Fr(gor[i]) * b[i] for i in range(N))
        v += sum(Fr(gor[N + k]) * (b[i] | b[j]) for k, (i, j) in enumerate(pairs))
        out.append(v)
    return out


neus = [setfun(n['g_or']) for n in sup['neurons']]
K = len(neus)
basis = [setfun([1 if t == u else 0 for t in range(N + len(pairs))]) for u in range(N + len(pairs))]
rows, rhs = [], []
for S in range(1, NS):
    rows.append([max(g[S], 0) for g in neus] + [b[S] for b in basis]); rhs.append(Fr(1 if S else 0))
for perm in itertools.permutations(range(N)):
    masks, m = [], 0
    for j in range(N - 1):
        m |= 1 << perm[j]; masks.append(m)
    cut = []
    for k, g in enumerate(neus):
        v = [g[s] for s in masks]
        if any(x > 0 for x in v) and any(x < 0 for x in v):
            cut.append((k, v))
    groups = []
    for k, v in cut:
        for gp in groups:
            w = gp[0][1]
            r = [x / y for x, y in zip(v, w) if y != 0]
            if all((x == 0) == (y == 0) for x, y in zip(v, w)) and len(set(r)) == 1:
                gp.append((k, v, abs(r[0]))); break
        else:
            groups.append([(k, v, Fr(1))])
    for gp in groups:
        row = [Fr(0)] * (K + len(basis))
        for k, v, lam in gp:
            row[k] = lam
        rows.append(row); rhs.append(Fr(0))
# Gaussian elimination
ncol = K + len(basis)
A = [r[:] + [b] for r, b in zip(rows, rhs)]
piv, r = [], 0
for c in range(ncol):
    p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
    if p is None: continue
    A[r], A[p] = A[p], A[r]
    inv = 1 / A[r][c]
    A[r] = [x * inv for x in A[r]]
    for i in range(len(A)):
        if i != r and A[i][c] != 0:
            f = A[i][c]
            A[i] = [x - f * y for x, y in zip(A[i], A[r])]
    piv.append(c); r += 1
if any(all(x == 0 for x in row[:-1]) and row[-1] != 0 for row in A):
    print('INCONSISTENT: support has no exact solution'); sys.exit(1)
sol = [Fr(0)] * ncol
for i, c in enumerate(piv):
    sol[c] = A[i][-1]          # free variables set to 0
d, rr = sol[:K], sol[K:]
print('exact d', [str(x) for x in d])
# real data: G = sum_i gi x_i + sum gij max(x_i,x_j);  max(x_i,x_j) = x_j + relu(x_i - x_j)
def real(vec):
    l = [Fr(vec[i]) for i in range(N)]
    a = {}
    for k, (i, j) in enumerate(pairs):
        c = Fr(vec[N + k])
        if c:
            l[j] += c; a[(i, j)] = a.get((i, j), 0) + c
    return l, a
NEURONS = [(d[k], *real(sup['neurons'][k]['g_or'])) for k in range(K) if d[k] != 0]
R = real(rr)
spec = importlib.util.spec_from_file_location('cert', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'dfs', 'h4-general-neurons', 'r2_certify.py'))
cert = importlib.util.module_from_spec(spec); spec.loader.exec_module(cert)
nreg, fails = cert.certify(N, R, NEURONS)
if fails:
    print('CERTIFICATION FAILED'); sys.exit(1)
units = []
for dk, l, a in NEURONS:
    units.append({'coef': str(dk), 'head': [str(x) for x in l], 'pairs': [[i, j, str(c)] for (i, j), c in a.items()]})
aux = [{'coef': str(c), 'kind': 'lin', 'i': i} for i, c in enumerate(R[0]) if c] + \
      [{'coef': str(c), 'kind': 'pair', 'i': i, 'j': j} for (i, j), c in R[1].items() if c]
json.dump({'name': sys.argv[2], 'N': N, 'source': 'research/sN/kN/chainlp.py + cert_exact.py (%s)' % sys.argv[1],
           'units': units, 'aux': aux}, open(sys.argv[3], 'w'), indent=1)
print('CERTIFIED: %d neurons, written %s' % (len(units), sys.argv[3]))
