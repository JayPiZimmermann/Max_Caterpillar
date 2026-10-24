"""Exact tools for second-layer neurons over the braid first layer.

A neuron is sigma(g), g(x) = b + sum_i a_i x_i + sum_{i<j} w_ij sigma(x_i - x_j)
(arbitrary real coefficients).  Parameter vector layout: [b, a_0..a_{N-1}, w_ij (i<j lex)].
A k-locality L = (T, rho): T tied at the top, outside coordinates strictly below in
the order rho (tuple, highest first).  cone_rows(L) are the linear forms that must
vanish for g to vanish identically on the cone C_L (necessary for passing L).
"""
from fractions import Fraction as Fr
from itertools import combinations, permutations

def pairs(N):
    return list(combinations(range(N), 2))

def nvars(N):
    return 1 + N + N*(N-1)//2

def pidx(N):
    return {p: 1 + N + k for k, p in enumerate(pairs(N))}

def cone_rows(N, T, rho):
    """Rows (lists of ints) whose vanishing <=> g == 0 on C_(T,rho)."""
    P = pidx(N)
    height = {t: 0 for t in T}
    for r, o in enumerate(rho):
        height[o] = -(r + 1)
    rows = []
    rb = [0]*nvars(N); rb[0] = 1; rows.append(rb)
    # coefficient of s
    rs = [0]*nvars(N)
    for t in T:
        rs[1+t] += 1
    for (i, j), k in P.items():
        if height[i] > height[j]:
            # active: contributes w*(x_i - x_j)
            if i in T: rs[k] += 1
            if j in T: rs[k] -= 1
    rows.append(rs)
    for o in rho:
        r = [0]*nvars(N); r[1+o] += 1
        for (i, j), k in P.items():
            if height[i] > height[j]:
                if i == o: r[k] += 1
                if j == o: r[k] -= 1
        rows.append(r)
    return rows

def localities(N, m):
    for T in combinations(range(N), m):
        rest = [o for o in range(N) if o not in T]
        for rho in permutations(rest):
            yield T, rho

def rref(rows):
    """Exact RREF over Q; returns (reduced rows, pivot columns)."""
    M = [[Fr(x) for x in r] for r in rows]
    piv = []
    r = 0
    ncol = len(M[0]) if M else 0
    for c in range(ncol):
        p = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                p = i; break
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x*inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f*y for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
        if r == len(M): break
    return M[:r], piv

def nullspace(rows, n):
    if not rows:
        return [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    R, piv = rref(rows)
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [Fr(0)]*n; v[f] = Fr(1)
        for row, pc in zip(R, piv):
            v[pc] = -row[f]
        basis.append(v)
    return basis

def germ(N, T, theta):
    """Germ of g at a generic point of the T-top stratum (outside strictly below):
    returns (v dict t->coef, w dict (i,j)->coef for pairs inside T)."""
    P = pidx(N)
    v = {t: theta[1+t] for t in T}
    for (i, j), k in P.items():
        if i in T and j not in T:
            v[i] += theta[k]
        # i not in T, j in T: x_i < x_j, inactive
    wT = {(i, j): theta[P[(i, j)]] for (i, j) in combinations(T, 2)}
    return v, wT

def evalG(v, wT, z):
    s = sum(v[t]*z[t] for t in v)
    for (i, j), c in wT.items():
        d = z[i] - z[j]
        if d > 0: s += c*d
    return s

def mixed_diff_sigma(v, wT, T, delta=Fr(1, 1000), center=None):
    """m-th mixed finite difference of sigma(G) over the box centered at `center`
    (default: a fixed generic small offset), side delta, in the T coordinates."""
    m = len(T)
    if center is None:
        center = {t: Fr(0) for t in T}
    tot = Fr(0)
    for bits in range(1 << m):
        z = {}
        sgn = 1
        for k, t in enumerate(T):
            if bits >> k & 1:
                z[t] = center[t] + delta/2
            else:
                z[t] = center[t] - delta/2; sgn = -sgn
        val = evalG(v, wT, z)
        tot += sgn * (val if val > 0 else 0)
    return tot
