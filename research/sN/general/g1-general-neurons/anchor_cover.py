"""Check (exact rationals) that the anchor family
   g_{a,l}(x) = sum_{j != a} c^{(l)}_j sigma(x_j - x_a),  c^{(l)}_j = s_l(j) 2^j,
   s_l(j) = (-1)^{bit l of j},  a in [N], 0 <= l < ceil(log2 N),
passes every 3-locality of the paper (NOTE.md stencil: T={a<b<c} at 0, outside at -B^rho,
q+- = p +- eps(e_a+e_b), d = e_a-e_b, J g(q) = g(q+dd)+g(q-dd)-2g(q), Lambda = J(q+)-J(q-)),
i.e. Lambda sigma(g) != 0 for some neuron of the family.  Also prints how many neurons pass.
Usage: python anchor_cover.py N [bits|mid]"""
import sys, itertools, math
from fractions import Fraction as Fr
N = int(sys.argv[1]); L = max(1, math.ceil(math.log2(N)))
relu = lambda t: t if t > 0 else Fr(0)
fam = []
MODE = sys.argv[2] if len(sys.argv) > 2 else 'bits'
if MODE == 'bits':
    for a in range(N):
        for l in range(L):
            c = [Fr(0) if j == a else Fr((-1) ** ((j >> l) & 1) * 2 ** j) for j in range(N)]
            fam.append((a, l, c))
else:  # 'mid': N-2 neurons, anchor a = 1..N-2, c_j = +2^j (j > a), -2^j (j < a)
    for a in range(1, N - 1):
        c = [Fr(0) if j == a else Fr((1 if j > a else -1) * 2 ** j) for j in range(N)]
        fam.append((a, 0, c))
def neuron(c, a, x):
    return relu(sum(c[j] * relu(x[j] - x[a]) for j in range(N) if j != a))
B = 10; eps = Fr(1, 64); dl = eps / 2
tot = 0; minpass = None; bad = 0
for T in itertools.combinations(range(N), 3):
    O = [v for v in range(N) if v not in T]
    for order in itertools.permutations(O):
        p = [Fr(0)] * N
        for r, o in enumerate(order):
            p[o] = Fr(-B ** (r + 1))
        a_, b_ = T[0], T[1]
        def pt(base, s):
            q = list(base); q[a_] += s; q[b_] += s; return q
        def J(f, q):
            qp = list(q); qp[a_] += dl; qp[b_] -= dl
            qm = list(q); qm[a_] -= dl; qm[b_] += dl
            return f(qp) + f(qm) - 2 * f(q)
        lam = lambda f: J(f, pt(p, eps)) - J(f, pt(p, -eps))
        assert lam(lambda x: max(x)) == 2 * dl
        k = sum(1 for (a, l, c) in fam if lam(lambda x: neuron(c, a, x)) != 0)
        tot += 1; bad += (k == 0); minpass = k if minpass is None else min(minpass, k)
print('N', N, 'family size', len(fam), 'localities', tot, 'unpassed', bad, 'min #passing neurons', minpass)
