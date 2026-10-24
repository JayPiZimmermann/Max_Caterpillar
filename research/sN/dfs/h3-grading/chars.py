"""Character values (Murnaghan-Nakayama) of V_N/A_N and its graded pieces, and the permutation
character of the dictionary (number of keys fixed by g), per cycle type."""
import sys, json
from functools import lru_cache
from kostka import partitions, conj, flam
from common import keys
from sym import act_key
def mn(lam, rho):
    # character chi^lam(rho) via border-strip removal on beta-sets
    @lru_cache(None)
    def rec(lam, rho):
        if not rho: return 1 if sum(lam) == 0 else 0
        r, rest = rho[0], rho[1:]
        n = len(lam); beta = [lam[i] + (n - 1 - i) for i in range(n)]
        tot = 0; bs = set(beta)
        for b in beta:
            if b - r >= 0 and (b - r) not in bs:
                sign = (-1) ** sum(1 for c in beta if b - r < c < b)
                nb = sorted([c for c in beta if c != b] + [b - r], reverse=True)
                nl = tuple(nb[i] - (n - 1 - i) for i in range(n))
                tot += sign * rec(nl, rest)
        return tot
    return rec(tuple(lam), tuple(rho))
def perm_of_type(N, rho):
    g = list(range(N)); s = 0
    for r in rho:
        for t in range(r): g[s + t] = s + (t + 1) % r
        s += r
    return tuple(g)
if __name__ == '__main__':
    N = int(sys.argv[1]); mult = json.loads(sys.argv[2])   # {"lam string": m}
    Ps = list(partitions(N))
    ks = keys(N); kset = set(ks)
    for rho in Ps:
        chi = sum(m * mn(tuple(int(c) for c in l), rho) for l, m in mult.items())
        g = perm_of_type(N, rho)
        fixed = sum(1 for k in ks if act_key(g, k) == k)
        print(''.join(map(str, rho)), 'chi_V/A', chi, 'fixed keys', fixed)
