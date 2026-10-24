"""Generic symmetric 'top' test.
A family = generator of neurons on the identity chamber x_1>...>x_N, each given as
(type, a) where a = integer coefficient vector of the linear form of g on the chamber
(sum a = 0).  Weights are constant on types (S_N-orbits).  Conditions:
 (i) crossing cancellation per direction class  -> F braid-PL symmetric = L-statistic f
 (ii) ell(f) = sum_r (-1)^(r-1) C(N-1,r-1) f_r  != 0   (top coefficient of max_N mod lower max_T)
Also reports whether F = max_N exactly modulo symmetric V1 is solvable ('exact')."""
from math import comb, gcd
from fractions import Fraction as Fr
from linalg import solve

def analyze(N, neurons, verbose=True, want_exact=False):
    types = {}; lin = {}; cross = {}
    def add(dct, key, var, c):
        e = dct.setdefault(key, {}); e[var] = e.get(var, 0) + c
    for t, a, mult in neurons:
        if t not in types: types[t] = len(types)
        var = types[t]
        D = []; s = 0
        for i in range(N - 1):
            s += a[i]; D.append(s)
        assert s + a[N - 1] == 0, 'not translation invariant'
        pos = any(d > 0 for d in D); neg = any(d < 0 for d in D)
        if pos and not neg:
            for i, d in enumerate(D):
                if d: add(lin, i, var, mult * d)
        elif pos and neg:
            g = 0
            for d in D: g = gcd(g, abs(d))
            first = next(d for d in D if d); sgn = 1 if first > 0 else -1
            key = tuple(sgn * d // g for d in D); lam = sgn * g
            add(cross, key, var, mult * abs(lam))
            if lam < 0:
                for i, d in enumerate(key):
                    if d: add(lin, i, var, mult * lam * d)
    nv = len(types)
    ellD = {}
    for r in range(1, N + 1):
        w = (-1) ** (r - 1) * comb(N - 1, r - 1)
        if r - 1 < N - 1: ellD[r - 1] = ellD.get(r - 1, 0) + w
        if r - 2 >= 0: ellD[r - 2] = ellD.get(r - 2, 0) - w
    ellrow = {}
    for i, w in ellD.items():
        for var, cc in lin.get(i, {}).items(): ellrow[var] = ellrow.get(var, 0) + w * cc
    rows = list(cross.values()); rhs = [0] * len(rows)
    ok, sol, piv, free = solve(rows + [ellrow], rhs + [1], nv)
    res = {'types': nv, 'cross': len(cross), 'top': ok, 'sol': sol, 'typenames': {v: k for k, v in types.items()}}
    if want_exact:
        A = nv; B = nv + 1
        rows2 = list(cross.values()); rhs2 = [0] * len(rows2)
        for j in range(N - 1):
            e = dict(lin.get(j, {}))
            e[A] = e.get(A, 0) + sum(N - i for i in range(1, j + 2))
            e[B] = e.get(B, 0) + (j + 1)
            rows2.append(e); rhs2.append(1)
        rows2.append({A: comb(N, 2), B: N}); rhs2.append(1)
        ok2, sol2, _, _ = solve(rows2, rhs2, nv + 2)
        res['exact'] = ok2; res['sol_exact'] = sol2
    if verbose:
        print('N', N, 'types', nv, 'cross classes', len(cross), 'top', ok, ('exact %s' % res['exact']) if want_exact else '')
    return res

def hinge(N, a, p, q, w):
    """add w*sigma(x_p - x_q) on identity chamber (positions 0-based; p<q means x_p>x_q)."""
    if p < q:
        a[p] += w; a[q] -= w
