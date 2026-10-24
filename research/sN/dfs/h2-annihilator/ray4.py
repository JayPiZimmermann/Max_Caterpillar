"""N=4: kink weights of V- and W-germs at the ray x0=(0,0,1,2) (exact)."""
from fractions import Fraction as F
import flint
from germs import Setup
S = Setup(4)
A = S.A
B = 1000
x0 = (0, 0, B, 2 * B)
def ev(vec, x):
    # vec: dict var->coef ; x: Fraction point
    row = S.eval_row_frac(x) if hasattr(S, 'eval_row_frac') else None
def eval_frac(vec, x):
    N = 4
    pi = tuple(sorted(range(N), key=lambda i: (x[i], i)))
    c = A.pidx[pi]
    t = [x[pi[j]] - x[pi[j - 1]] for j in range(1, N)]
    s = F(0)
    for j in range(N - 1):
        s += vec.get(A.var_lin(c, j), 0) * t[j]
    for pp in A.D[c]:
        v = sum(a * b for a, b in zip(pp, t))
        if v > 0:
            s += vec.get(A.var_kink(c, pp), 0) * v
    return s
def g(vec, u, v):
    dx = (u, F(0), (u - v) / 2, F(0))
    return eval_frac(vec, [a + b for a, b in zip(x0, dx)])
e = F(1, 7)
probes = {  # name: (point on half-line, second-difference direction)
 'L1+ (u=0,v>0)': ((0, 1), (1, 0)), 'L1- (u=0,v<0)': ((0, -1), (1, 0)),
 'L2+ (v=0,u>0)': ((1, 0), (0, 1)), 'L2- (v=0,u<0)': ((-1, 0), (0, 1)),
 'L3+ (u=v>0)': ((1, 1), (0, 1)), 'L3- (u=v<0)': ((-1, -1), (0, 1))}
def weights(vec):
    out = []
    for name, ((pu, pv), (du, dv)) in probes.items():
        pu, pv = F(pu) * 5, F(pv) * 5
        w = (g(vec, pu + e * du, pv + e * dv) + g(vec, pu - e * du, pv - e * dv) - 2 * g(vec, pu, pv)) / e
        out.append(w)
    return out
VW = [weights(v) for v in S.Vrows]
Q=lambda f: flint.fmpq(f.numerator, f.denominator)
M = flint.fmpq_mat([[Q(w[i]) for w in VW] for i in range(6)])
print('rank of V-germ weights', M.rank())
# W basis vectors as dicts
C = A.constraints()
Cz = flint.fmpz_mat(len(C), A.nvars)
for r, row in enumerate(C):
    for c, x in row.items():
        Cz[r, c] = x
XW, nW = Cz.nullspace()
print('exact dim W', nW)
WW = []
for j in range(nW):
    vec = {i: int(XW[i, j]) for i in range(A.nvars) if int(XW[i, j])}
    WW.append(weights(vec))
MW = flint.fmpq_mat([[Q(w[i]) for w in WW] for i in range(6)])
print('rank of W-germ weights', MW.rank())
# left null space of V weights
T = M.transpose()
Z = flint.fmpz_mat([[int(T[i, j] * 2) for j in range(6)] for i in range(T.nrows())])
X, nul = Z.nullspace()
print('relations among the 6 weights valid on V (columns):')
for j in range(nul):
    print([int(X[i, j]) for i in range(6)], list(probes))
Z2 = flint.fmpz_mat([[int(w[i] * 2) for i in range(6)] for w in WW])
X2, nul2 = Z2.nullspace()
print('relations valid on W:')
for j in range(nul2):
    print([int(X2[i, j]) for i in range(6)])
