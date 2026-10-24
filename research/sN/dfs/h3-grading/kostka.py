"""Partitions, Kostka numbers, and decomposition of dims of (twisted) Young-subgroup fixed spaces.
dim V^{S_mu} = sum_lam K[lam][mu] m_lam ;  dim (V (x) sgn)^{S_mu} = sum_lam K[lam'][mu] m_lam."""
from fractions import Fraction
from functools import lru_cache
def partitions(n, mx=None):
    if mx is None: mx = n
    if n == 0: yield (); return
    for k in range(min(n, mx), 0, -1):
        for r in partitions(n - k, k): yield (k,) + r
def conj(l):
    return tuple(sum(1 for x in l if x > i) for i in range(l[0])) if l else ()
def kostka(lam, mu):
    # count SSYT of shape lam, content mu: fill numbers 1..len(mu) successively as horizontal strips
    @lru_cache(None)
    def rec(shape, t):
        if t == len(mu):
            return 1 if shape == lam else 0
        tot = 0
        # add horizontal strip of size mu[t] to shape staying inside lam
        def strips(i, rem, cur):
            nonlocal tot
            if i == len(lam):
                if rem == 0: tot_add(tuple(cur))
                return
            prev_old = shape[i - 1] if i > 0 else 10**9
            lo = shape[i] if i < len(shape) else 0
            hi = min(lam[i], prev_old)  # horizontal strip: new row i <= old row i-1
            for v in range(lo, hi + 1):
                if v - lo <= rem:
                    strips(i + 1, rem - (v - lo), cur + [v])
        res = []
        def tot_add(s): res.append(s)
        strips(0, mu[t], [])
        return sum(rec(s, t + 1) for s in res)
    return rec(tuple(0 for _ in lam), 0)
def flam(lam):
    return kostka(lam, (1,) * sum(lam))
def solve(N, fixed_triv, fixed_sgn=None):
    """fixed_triv: dict mu -> dim V^{S_mu}; returns m_lam for lam in upward-closed known set."""
    Ps = list(partitions(N))
    m = {}
    # process lam in decreasing dominance (lexicographic order is a linear extension)
    for lam in Ps:
        if lam in fixed_triv:
            val = fixed_triv[lam] - sum(kostka(l, lam) * m[l] for l in m if l != lam)
            m[lam] = val
    if fixed_sgn:
        for mu in Ps:
            lam = conj(mu)
            if mu in fixed_sgn and lam not in m:
                val = fixed_sgn[mu] - sum(kostka(conj(l), mu) * m[l] for l in m)
                m[lam] = val
    return m
if __name__ == '__main__':
    for N in (3, 4, 5, 6):
        print(N, [(l, flam(l)) for l in partitions(N)])
