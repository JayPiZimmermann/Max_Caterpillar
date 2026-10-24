"""Check Lambda_rho U_pi = [pi = rho] exactly as in Dimension.lean:
z_0 = z_b = 2r, z_{rho(k)} = 2k, step 1, Lambda = D_0 D_b D_c at z, c = rho(r)."""
import itertools, sys
from lam import unit
for N in range(3, 8):
    r = N - 2; b = N - 1; bad = 0
    perms = list(itertools.permutations(range(1, b)))
    for rho in perms:
        z = [2 * r] * N
        for k, l in enumerate(rho): z[l] = 2 * (k + 1)
        c = rho[-1]
        for pi in perms:
            tot = 0
            for e in itertools.product((0, 1), repeat=3):
                x = z[:]; x[0] += e[0]; x[b] += e[1]; x[c] += e[2]
                tot += (-1) ** (3 - sum(e)) * unit(0, list(pi) + [b], x)
            if tot != (1 if pi == rho else 0): bad += 1
    print(N, len(perms), "mismatches", bad)
