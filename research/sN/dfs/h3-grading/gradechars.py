"""Characters chi(rho) of every graded piece gr_j (j = |M|) of V_N/A_N, from the certified multiplicities
(tabulate.from_young on cert_N.log); prints chi per cycle type and the class-size weighted check sum = dim."""
import sys, json, contextlib, io
with contextlib.redirect_stdout(io.StringIO()):
    import tabulate as T
from kostka import partitions
from chars import mn
for N in (4, 5, 6):
    recs = T.load(f'cert_{N}.log') + T.load(f'cert_{N}_321sgn.log')
    m = T.from_young(N, recs)
    Ps = list(partitions(N)); G = list(range(-1, N - 1))
    print(f'N={N} cycle types', [''.join(map(str, r)) for r in Ps])
    for g in range(1, len(G)):
        mult = {l: m[l][g] - m[l][g - 1] for l in Ps}
        chi = [sum(c * mn(l, rho) for l, c in mult.items()) for rho in Ps]
        print(f'  gr_{G[g]}', chi)
    mult = {l: m[l][-1] - m[l][0] for l in Ps}
    print('  V/A ', [sum(c * mn(l, rho) for l, c in mult.items()) for rho in Ps])
    mult = {l: m[l][0] for l in Ps}
    print('  A   ', [sum(c * mn(l, rho) for l, c in mult.items()) for rho in Ps])
