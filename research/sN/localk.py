"""Triple-locality lower bound for s_N.

Locality L = (T, order): x_T tied at 0, all other coordinates strictly below in
the given order (generic gaps). Germ of a unit at such a point; class modulo
span{linear, relu(y_a-y_b), relu(y_a-y_c), relu(y_b-y_c)}. A unit "serves" L if
its class is nonzero. Every expansion of max_N must contain, for each L, a unit
serving L (max_N's germ there is max_3, whose class is nonzero).
"""
import sys, itertools, random
from fractions import Fraction
sys.path.insert(0, 'scripts')
from vocabulary_search import dictionary, is_auxiliary, relu

N = int(sys.argv[1]); k = int(sys.argv[2])
K0, _ = dictionary(N)
units = [k for k in K0 if not is_auxiliary(k)]
print('units', len(units))

# 3-variable test points (integers), basis of the excluded span
rng = random.Random(1)
pts = [tuple(rng.randint(-50, 50) for _ in range(k)) for _ in range(30 * k * k)]
def span_rows(y):
    return list(y) + [relu(y[i] - y[j]) for i in range(k) for j in range(i + 1, k)]
import numpy as np
B = np.array([span_rows(y) for y in pts], dtype=float)

def rank(M):
    return np.linalg.matrix_rank(M, tol=1e-7)
rB = rank(B)

def nonzero_class(vals):
    return rank(np.column_stack([B, np.array(vals, dtype=float)])) > rB

def germ_class(key, T, order):
    h, M = key
    pos = {}
    for t in T:
        pos[t] = 0
    for rank_, o in enumerate(order):
        pos[o] = -(rank_ + 1)          # strictly below, decreasing in order
    v = list(h)
    inner = []
    for (i, j) in M:
        if i in T and j in T:
            inner.append((i, j))
        elif pos[i] > pos[j]:
            v[i] += 1; v[j] -= 1          # active, linear
    if any(v[o] for o in range(N) if o not in T):
        return None
    vals = []
    for y in pts:
        yy = dict(zip(T, y))
        s = sum(v[t] * yy[t] for t in T) + sum(relu(yy[i] - yy[j]) for i, j in inner)
        vals.append(relu(s))
    return tuple(vals) if nonzero_class(vals) else None

locs = []
for T in itertools.combinations(range(N), k):
    rest = [o for o in range(N) if o not in T]
    for order in itertools.permutations(rest):
        locs.append((T, order))
print('localities', len(locs))
serve = {}
cover = [set() for _ in locs]
for u, key in enumerate(units):
    for l, (T, order) in enumerate(locs):
        if germ_class(key, T, order) is not None:
            cover[l].add(u)
cnt = [0] * len(units)
for l in range(len(locs)):
    for u in cover[l]:
        cnt[u] += 1
print('max localities served by one unit', max(cnt), 'min servers per locality', min(len(c) for c in cover))
import pickle
pickle.dump((units, locs, cover), open(f'research/sN/data/localk_{N}_{k}.pkl', 'wb'))

# exact hitting set via scipy milp
from scipy.optimize import milp, LinearConstraint, Bounds
A = np.zeros((len(locs), len(units)))
for l, c in enumerate(cover):
    for u in c:
        A[l, u] = 1
res = milp(c=np.ones(len(units)), constraints=LinearConstraint(A, lb=1, ub=np.inf),
           integrality=np.ones(len(units)), bounds=Bounds(0, 1), options={'time_limit': 600})
print('hitting set', res.status, res.fun, 'trivial bound', len(locs) / max(cnt))
