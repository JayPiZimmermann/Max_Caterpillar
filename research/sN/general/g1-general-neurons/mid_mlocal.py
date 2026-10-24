"""Exact check for m-localities, 3 <= m <= N: for every m-set T (top, tied at 1; outside at
generic values in (0,1)), the middle-anchor neuron g_a (a = second-smallest element of T,
c_j = +2^j for j > a, -2^j for j < a) satisfies g_a = 0 near the stratum point p and the
m-th mixed difference of sigma(g_a) over the box constructed in the proof is nonzero.
Box: z0 = p + h*(u-vector with sum_t c_t u_t = 0, u_t > 0), lambda = gradient of g_a at z0,
corner chosen so only the all-'up' corner (after flipping negative directions) is positive.
Usage: python mid_mlocal.py N"""
import sys, itertools
from fractions import Fraction as Fr
N = int(sys.argv[1]); relu = lambda t: t if t > 0 else Fr(0)
def g(a, x):
    return sum(((1 if j > a else -1) * 2 ** j) * relu(x[j] - x[a]) for j in range(N) if j != a)
bad = 0; tot = 0
for m in range(3, N + 1):
    for T in itertools.combinations(range(N), m):
        a = T[1]; rest = [t for t in T if t != a]
        c = {t: (1 if t > a else -1) * 2 ** t for t in rest}
        p = [Fr(1)] * N; k = 1
        for o in range(N):
            if o not in T: p[o] = Fr(k, N + 2); k += 1      # outside strictly below 1, all > 0
        assert g(a, p) == 0
        # u_t > 0 with sum c_t u_t = 0: u = 1 for all but the minimum element t0 (negative c)
        t0 = rest[0]; u = {t: Fr(1) for t in rest}; u[t0] = Fr(sum(c[t] for t in rest if t != t0), -c[t0])
        assert u[t0] > 0 and sum(c[t] * u[t] for t in rest) == 0
        h = Fr(1, 10 ** 6); z0 = list(p)
        for t in rest: z0[t] += h * u[t]
        lam = {t: Fr(c[t]) for t in rest}; lam[a] = -Fr(sum(c[t] for t in rest))
        assert all(v != 0 for v in lam.values())
        mu = {t: abs(v) for t, v in lam.items()}; dl = h / 10 ** 4
        # corner: start with directions flipped for negative lambda; offset b
        base = list(z0); tot_mu = sum(mu.values()); mmin = min(mu.values())
        bshift = -(tot_mu - mmin / 2) * dl                    # value of lambda.(z-z0) at start corner
        # place start corner so that lambda.(start - z0) = bshift: move along coordinate a
        base[a] += bshift / lam[a]
        Lam = Fr(0)
        for eps in itertools.product((0, 1), repeat=m):
            x = list(base)
            for e, t in zip(eps, T):
                x[t] += (dl if lam[t] > 0 else -dl) * e
            Lam += (-1) ** (m - sum(eps)) * relu(g(a, x))
        tot += 1; bad += (Lam == 0)
print('N', N, 'm-sets checked (all m>=3)', tot, 'zero mixed differences', bad)
