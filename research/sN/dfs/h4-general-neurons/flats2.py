"""Flats of the 3-locality equation system for general neurons (model A) with their
generic passing sets, and covering numbers.

For every flat W_S (S a set of 3-localities, reached by BFS), take R random rational
points of W_S and record the union of their exact passing sets (passing is an open
condition in the neuron weights, so each recorded locality is generically passed on
W_S; a locality missed by all R points could only be one whose degenerate locus is
hit R times - measured, probability ~0).  Then compute the minimum number of passing
sets covering all localities (exact set cover over the recorded sets).

Every neuron g has P(g) contained in the generic passing set of the flat W_{P(g)}, so
min cover over flats <= s^gen_N is a lower bound (modulo the random-point step).
Usage: python flats2.py N [R] [seed]
"""
import sys, itertools, random, pickle, time
from fractions import Fraction as Fr
from passing import localities, passes

P = 2_147_483_629


def rref_p(rows, nv):
    M = [[x % P for x in r] for r in rows]
    piv = []
    r = 0
    for c in range(nv):
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = pow(M[r][c], P - 2, P)
        M[r] = [x * inv % P for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(x - f * y) % P for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    return M[:r], piv


def nullspace_q(rows, nv):
    M = [[Fr(x) for x in r] for r in rows]
    piv = []
    r = 0
    for c in range(nv):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(nv) if c not in piv]
    B = []
    for f in free:
        v = [Fr(0)] * nv
        v[f] = Fr(1)
        for row, pc in zip(M[:r], piv):
            v[pc] = -row[f]
        B.append(v)
    return B


def main(N, R=2, seed=1):
    rnd = random.Random(seed)
    pr = list(itertools.combinations(range(N), 2))
    idx = {p: i for i, p in enumerate(pr)}
    nv = len(pr) + N
    locs = list(localities(N))
    LR = []
    for T, order in locs:
        rows = []
        above = list(T)
        for o in order:
            r = [0] * nv
            for j in above:
                r[idx[(min(o, j), max(o, j))]] += 1
            r[len(pr) + o] -= 1
            rows.append(r)
            above.append(o)
        LR.append(rows)
    base = [[-1] * len(pr) + [1] * N]
    seen = {}
    frontier = [base]
    t0 = time.time()
    while frontier:
        new = []
        for rows in frontier:
            Rm, piv = rref_p(rows, nv)
            key = tuple(map(tuple, Rm))
            if key in seen:
                continue
            rk = len(Rm)
            cl = []
            for i in range(len(locs)):
                if len(rref_p(Rm + LR[i], nv)[0]) == rk:
                    cl.append(i)
            B = nullspace_q(rows, nv)
            pas = 0
            if B:
                for _ in range(R):
                    cf = [rnd.randint(-40, 40) for _ in B]
                    pt = [sum(c * b[j] for c, b in zip(cf, B)) for j in range(nv)]
                    a = {p: pt[i] for i, p in enumerate(pr) if pt[i] != 0}
                    kappa = pt[len(pr):]
                    for i in cl:
                        if not (pas >> i) & 1 and passes(a, kappa, *locs[i]):
                            pas |= 1 << i
            seen[key] = (rk, sum(1 << i for i in cl), pas)
            # integer basis rows: keep original rows that are independent
            ind = []
            rr = 0
            for r_ in rows:
                if len(rref_p(ind + [r_], nv)[0]) > rr:
                    ind.append(r_)
                    rr += 1
            for i in range(len(locs)):
                if i not in cl:
                    new.append(ind + LR[i])
        frontier = new
        print('flats so far', len(seen), 'time %.0f' % (time.time() - t0), flush=True)
    sets = sorted({v[2] for v in seen.values()}, key=lambda s: -bin(s).count('1'))
    # remove dominated
    maxi = []
    for s in sets:
        if not any((s | m) == m for m in maxi):
            maxi.append(s)
    full = (1 << len(locs)) - 1
    print('N', N, 'localities', len(locs), 'flats', len(seen), 'distinct passing sets', len(sets),
          'maximal', len(maxi), 'max |P|', bin(sets[0]).count('1'))
    # min cover
    def cover(k, cur, start):
        if cur == full:
            return True
        if k == 0:
            return False
        # pick lowest uncovered locality, branch over sets containing it
        u = (~cur & full) & -(~cur & full)
        for m in maxi:
            if m & u and cover(k - 1, cur | m, 0):
                return True
        return False
    for k in range(1, 8):
        if cover(k, 0, 0):
            print('min cover by passing sets:', k)
            break
        print('no cover with', k)
    pickle.dump({'locs': locs, 'flats': seen, 'maximal': maxi}, open('flats2_N%d.pkl' % N, 'wb'))


if __name__ == '__main__':
    N = int(sys.argv[1])
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    main(N, R)
