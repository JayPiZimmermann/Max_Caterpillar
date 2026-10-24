"""Maximum number of 3-localities a single general neuron passes (model A).

Enumerates the flats W_S = {(a,kappa): E_L holds for all L in S} reachable by adding
localities one at a time (BFS over the intersection lattice, deduplicated by RREF mod p),
and at a random rational point of each flat counts passing localities exactly.
The count at a random point is an exact count for THAT point (a certified witness);
treating it as the generic value of the flat is a measured step (random point).
Usage: python maxpass.py N [maxflats]
"""
import sys, itertools, random
from fractions import Fraction as Fr
import numpy as np
import sympy
from passing import localities, passes

P = 2_147_483_629


def var_index(N):
    pr = list(itertools.combinations(range(N), 2))
    idx = {p: i for i, p in enumerate(pr)}
    return pr, idx, len(pr) + N


def loc_rows(N, T, order, idx, nv):
    rows = []
    above = list(T)
    npair = len(idx)
    for o in order:
        r = [0] * nv
        for j in above:
            r[idx[(min(o, j), max(o, j))]] += 1
        r[npair + o] -= 1
        rows.append(r)
        above.append(o)
    return rows


def rref_modp(M):
    A = np.array(M, dtype=np.int64) % P
    rows, cols = A.shape
    r = 0
    piv = []
    for c in range(cols):
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        p = r + nz[0]
        if p != r:
            A[[r, p]] = A[[p, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy(); col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            A[nzr] = (A[nzr] - (col[nzr, None] * A[r][None, :]) % P) % P
        piv.append(c)
        r += 1
        if r == rows:
            break
    return A[:r], piv


def intbasis(rows, piv_rows=None):
    """Independent integer subset of rows (greedy, rank mod p)."""
    out = []
    rk = 0
    for r in rows:
        t = out + [r]
        k = len(rref_modp(t)[0])
        if k > rk:
            out, rk = t, k
    return out


def main(N, maxflats=10**6, seed=1):
    rnd = random.Random(seed)
    pr, idx, nv = var_index(N)
    base = [[1 if i < len(pr) else 0 for i in range(nv)]]
    base[0] = [-1] * len(pr) + [1] * N  # sum kappa = sum a
    locs = list(localities(N))
    LR = [loc_rows(N, T, o, idx, nv) for T, o in locs]
    best = (-1, None)
    seen = set()
    frontier = [base]
    nflat = 0
    hist = {}
    while frontier and nflat < maxflats:
        new = []
        for rows in frontier:
            R, piv = rref_modp(rows)
            key = R.tobytes()
            if key in seen:
                continue
            seen.add(key)
            nflat += 1
            rk = len(R)
            # closure
            cl = [i for i in range(len(locs)) if len(rref_modp(np.concatenate([R, LR[i]]))[0]) == rk]
            # random rational point of flat (over Q: use sympy on the original integer rows)
            Mq = sympy.Matrix(rows)
            ns = Mq.nullspace()
            if not ns:
                continue
            pt = sum((rnd.randint(-30, 30) * v for v in ns), sympy.zeros(nv, 1))
            vals = [Fr(int(sympy.fraction(x)[0]), int(sympy.fraction(x)[1])) for x in pt]
            a = {p: vals[i] for i, p in enumerate(pr) if vals[i] != 0}
            kappa = vals[len(pr):]
            cnt = sum(1 for i in cl if passes(a, kappa, *locs[i]))
            hist[cnt] = hist.get(cnt, 0) + 1
            if cnt > best[0]:
                best = (cnt, (a, kappa, [locs[i] for i in cl], rk))
                print('flat', nflat, 'rank', rk, 'closure', len(cl), 'passing', cnt, flush=True)
            for i in range(len(locs)):
                if i not in cl:
                    new.append(intbasis(rows, piv_rows=None) + LR[i])
        frontier = new
    print('N', N, 'flats', nflat, 'localities', len(locs), 'max passing', best[0])
    print('hist', sorted(hist.items()))
    a, kappa, cl, rk = best[1]
    print('witness a', {k: str(v) for k, v in a.items()}, 'kappa', [str(k) for k in kappa])
    return best


if __name__ == '__main__':
    N = int(sys.argv[1])
    mf = int(sys.argv[2]) if len(sys.argv) > 2 else 10**6
    main(N, mf)
