"""Model (A) helpers: the paper's first hidden layer Phi for N inputs and conversion of
neuron inputs g = <l,x> + sum_{i<j} a_ij relu(x_i - x_j) + alpha relu(x_0) into rows on Phi.
Phi order: relu(x0), relu(-x0), relu(x_i - x0) (i=1..N-1), relu(x_i - x_j) (i<j, lexicographic)."""
import itertools
from fractions import Fraction as Fr


def phi_rows(N):
    rows = []
    e = lambda i: [1 if t == i else 0 for t in range(N)]
    rows.append(e(0)); rows.append([-c for c in e(0)])
    for i in range(1, N):
        rows.append([a - b for a, b in zip(e(i), e(0))])
    for i, j in itertools.combinations(range(N), 2):
        rows.append([a - b for a, b in zip(e(i), e(j))])
    return rows


def pair_index(N):
    return {p: 1 + N + t for t, p in enumerate(itertools.combinations(range(N), 2))}


def to_phi(N, l, a, alpha=0):
    """row w with w . Phi(x) = <l,x> + sum a_ij relu(x_i-x_j) + alpha relu(x0); a keys (i,j) any order."""
    P = pair_index(N)
    w = [Fr(0)] * (1 + N + N * (N - 1) // 2)
    l = [Fr(c) for c in l]
    for (i, j), c in a.items():
        c = Fr(c)
        if i < j:
            w[P[(i, j)]] += c
        else:  # relu(x_i-x_j) = relu(x_j-x_i) + x_i - x_j
            w[P[(j, i)]] += c; l[i] += c; l[j] -= c
    w[0] += Fr(alpha)
    # x0 = Phi0 - Phi1 ; x_i = x0 + relu(x_i-x0) - relu(x0-x_i)
    for i in range(N):
        c = l[i]
        if c == 0:
            continue
        w[0] += c; w[1] -= c
        if i > 0:
            w[1 + i] += c; w[P[(0, i)]] -= c
    return w


def s(x):
    x = Fr(x)
    return str(x.numerator) if x.denominator == 1 else '%d/%d' % (x.numerator, x.denominator)


def net_json(N, first, second, out):
    return {'N': N, 'first_layer': [[s(c) for c in r] for r in first],
            'second_layer': [[s(c) for c in r] for r in second], 'output': [s(c) for c in out]}
