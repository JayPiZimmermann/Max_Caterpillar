"""Rationalize free-remainder neurons (l, a) [a over pairs i<j, hinge relu(x_i-x_j)], d = +-1,
solve EXACTLY for the remainder R from the set-function equations R(1_S) = 1 - sum_k d_k relu(g_k(1_S))
(S nonempty), and write a spec for r2_certify.py / a model-(A) JSON via mk_from_spec.py.
Usage: python ray2spec.py in.npz den out_spec.py"""
import sys, itertools, numpy as np, sympy
from fractions import Fraction as Fr
N = 5
PAIRS = list(itertools.combinations(range(N), 2))
SETS = [frozenset(c) for r in range(1, N + 1) for c in itertools.combinations(range(N), r)]


def vS(l, a, S):
    return sum(l[i] for i in S) + sum(a[q] for q, (i, j) in enumerate(PAIRS) if i in S and j not in S)


def solve_R(neurons):
    rows, rhs = [], []
    for S in SETS:
        r = [1 if i in S else 0 for i in range(N)] + [1 if (i in S and j not in S) else 0 for i, j in PAIRS]
        rows.append(r)
        rhs.append(1 - sum(d * max(vS(l, a, S), 0) for d, l, a in neurons))
    M = sympy.Matrix(rows); b = sympy.Matrix([sympy.Rational(x.numerator, x.denominator) for x in rhs])
    sol, params = M.gauss_jordan_solve(b)
    assert len(params) == 0
    return [Fr(str(x)) for x in sol]


if __name__ == '__main__':
    z = np.load(sys.argv[1]); den = int(sys.argv[2])
    P, d = z['P'], z['d']
    neurons = []
    for k in range(len(P)):
        vals = [Fr(int(round(x * den)), den) for x in P[k]]
        l, a = vals[:N], vals[N:]
        if not any(vals):
            continue
        neurons.append((Fr(int(d[k])), l, a))
    try:
        R = solve_R(neurons)
    except Exception as e:
        print('no exact remainder:', e); sys.exit(1)
    with open(sys.argv[3], 'w') as f:
        f.write('from fractions import Fraction as Fr\nN = 5\n')
        f.write('R = (%r, %r)\n' % (R[:N], {p: R[N + q] for q, p in enumerate(PAIRS) if R[N + q]}))
        f.write('NEURONS = %r\n' % [(dd, l, {p: a[q] for q, p in enumerate(PAIRS) if a[q]}) for dd, l, a in neurons])
    print('wrote', sys.argv[3])
