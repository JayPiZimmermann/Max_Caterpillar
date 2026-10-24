"""Flats of the 3-locality equation system restricted to ONE order per T
(outside vertices ordered by index, smallest on top) -- 'fixed-order localities'.
Same method as flats2.py (exact ranks mod a prime, generic passing sets recorded by
R random rational points of each flat: MEASURED), reports the largest passing set
(max number of T a single general neuron passes) and the min cover number, which is
a lower bound for the number of general neurons (modulo the random-point step).
Usage: python r2_fo_flats.py N [R] [maxflats]"""
import sys, itertools, random, time
import flats2
from passing import passes

def fo_localities(N):
    for T in itertools.combinations(range(N), 3):
        yield T, tuple(v for v in range(N) if v not in T)

def main(N, R=2, maxflats=10**7):
    flats2.localities = fo_localities  # monkeypatch the family
    import passing
    locs = list(fo_localities(N))
    rnd = random.Random(1)
    pr = list(itertools.combinations(range(N), 2)); idx = {p: i for i, p in enumerate(pr)}; nv = len(pr) + N
    LR = []
    for T, order in locs:
        rows = []; above = list(T)
        for o in order:
            r = [0] * nv
            for j in above: r[idx[(min(o, j), max(o, j))]] += 1
            r[len(pr) + o] -= 1; rows.append(r); above.append(o)
        LR.append(rows)
    base = [[-1] * len(pr) + [1] * N]
    seen = {}; frontier = [base]; t0 = time.time()
    while frontier and len(seen) < maxflats:
        new = []
        for rows in frontier:
            Rm, piv = flats2.rref_p(rows, nv); key = tuple(map(tuple, Rm))
            if key in seen: continue
            rk = len(Rm)
            cl = [i for i in range(len(locs)) if len(flats2.rref_p(Rm + LR[i], nv)[0]) == rk]
            B = flats2.nullspace_q(rows, nv); pas = 0
            for _ in range(R if B else 0):
                cf = [rnd.randint(-40, 40) for _ in B]
                pt = [sum(c * b[j] for c, b in zip(cf, B)) for j in range(nv)]
                a = {p: pt[i] for i, p in enumerate(pr) if pt[i] != 0}
                for i in cl:
                    if not (pas >> i) & 1 and passes(a, pt[len(pr):], *locs[i]): pas |= 1 << i
            seen[key] = (rk, sum(1 << i for i in cl), pas)
            ind = []; rr = 0
            for r_ in rows:
                if len(flats2.rref_p(ind + [r_], nv)[0]) > rr: ind.append(r_); rr += 1
            new += [ind + LR[i] for i in range(len(locs)) if i not in cl]
        frontier = new
        best = max(bin(v[2]).count('1') for v in seen.values())
        print('flats', len(seen), 'max |P| so far', best, '%.0fs' % (time.time() - t0), flush=True)
    sets = sorted({v[2] for v in seen.values()}, key=lambda s: -bin(s).count('1'))
    maxi = []
    for s in sets:
        if not any((s | m) == m for m in maxi): maxi.append(s)
    full = (1 << len(locs)) - 1
    print('N', N, 'T-count', len(locs), 'flats', len(seen), 'maximal', len(maxi), 'max |P|', bin(sets[0]).count('1'))
    for m in maxi[:5]: print('  ', [locs[i][0] for i in range(len(locs)) if m >> i & 1])
    def cover(k, cur):
        if cur == full: return True
        if k == 0: return False
        u = (~cur & full) & -(~cur & full)
        return any(m & u and cover(k - 1, cur | m) for m in maxi)
    for k in range(1, 12):
        if cover(k, 0): print('min cover:', k); break
        print('no cover with', k, flush=True)

if __name__ == '__main__':
    a = sys.argv[1:]
    main(int(a[0]), *(int(x) for x in a[1:]))
