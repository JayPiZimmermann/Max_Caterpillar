"""Balance functional Lambda*_d (kills every ridge germ in any direction, all affine germs)
and a pass counter for braid neurons given by edge weights w and kappa."""
from fractions import Fraction as Fr
from itertools import combinations
from braidlib import *
EPS = Fr(1, 10**9)
def phi(v, wT, z):
    s = evalG(v, wT, z)
    return s if s > 0 else 0
def lam_star(v, wT, T, i, j):
    """d = e_i + e_j (ray z_i = z_j > z_k), n = e_i - e_j; compare with -d."""
    def sd(sign):
        d = {t: Fr(0) for t in T}; d[i] = Fr(sign); d[j] = Fr(sign)
        zp = dict(d); zp[i] += EPS; zp[j] -= EPS
        zm = dict(d); zm[i] -= EPS; zm[j] += EPS
        return phi(v, wT, zp) + phi(v, wT, zm) - 2*phi(v, wT, d)
    return sd(1) - sd(-1)
def theta_from(N, w, kappa):
    """w: dict (i,j) i<j -> weight on sigma(x_i - x_j); kappa_o = a_o + sum_{j>o} w_oj."""
    th = [Fr(0)]*nvars(N); P = pidx(N)
    for p, x in w.items(): th[P[p]] = Fr(x)
    for o in range(N):
        th[1+o] = Fr(kappa[o]) - sum(Fr(w.get((o, j), 0)) for j in range(o+1, N))
    return th
def passes(N, m, th, mode="star"):
    """mode 'star': pass iff cone vanishes and Lambda*_d sigma(G) != 0 for SOME root ray d in T
    (superset of passing for any fixed choice); 'mixed': centered mixed m-th difference."""
    out = []
    n = len(th)
    for T, rho in localities(N, m):
        if any(sum(r[k]*th[k] for k in range(n)) != 0 for r in cone_rows(N, T, rho)):
            continue
        v, wT = germ(N, T, th)
        if mode == "mixed":
            ok = mixed_diff_sigma(v, wT, T) != 0
        else:
            ok = any(lam_star(v, wT, T, i, j) != 0 for i, j in combinations(T, 2))
        if ok: out.append((T, rho))
    return out
