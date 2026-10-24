"""Mod-p rank tools (numpy int64, p < 2^31)."""
import numpy as np
P = 2147483629
def rank_mod(M, p=P):
    M = np.array(M, dtype=np.int64) % p
    r = 0; rows, cols = M.shape
    for c in range(cols):
        if r == rows: break
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        i = r + nz[0]
        if i != r: M[[r, i]] = M[[i, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        others = np.nonzero(M[:, c])[0]
        others = others[others != r]
        if len(others):
            f = M[others, c][:, None]
            M[others] = (M[others] - (f * M[r][None, :]) % p) % p
        r += 1
    return r
