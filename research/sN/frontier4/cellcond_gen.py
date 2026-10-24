"""MEASURED probe (exact per instance): cell condition (PROOFS.md, 'What transfers', item 3) for
N = 5, (|J+|,|J-|,|J0|) = (1,1,5), J0 supports one of the two minimal C3+C4 families containing
a 3-support (best5/PROOFS.md H1(iii)):  F2 = {01,02,034,13,24},  F3 = {01,02,123,124,34}.
Pair rows: both orientations. 3-support rows: every primitive integer vector with that exact
support, coefficient sum 0 and entries in [-B, B].  Each instance is decided exactly as in
cellcond.py (FAIL = proof for that instance); the parameter grid itself is only a sample of the
continuous family, so 'all fail' is MEASURED evidence, not a proof.
Usage: python cellcond_gen.py B [samples]"""
import sys, itertools, random, math
from cellcond import cell_ok, rank

N = 5


def dirs(sup, B):
    out = []
    for c in itertools.product(range(-B, B + 1), repeat=len(sup)):
        if 0 in c or sum(c) != 0:
            continue
        if math.gcd(*[abs(v) for v in c]) != 1:
            continue
        r = [0] * N
        for i, v in zip(sup, c):
            r[i] = v
        out.append(r)
    return out


def main():
    B = int(sys.argv[1]); S = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    rng = random.Random(0)
    pts = [rng.sample(range(-10**6, 10**6), N) for _ in range(S)]
    fams = {'F2': [(0, 1), (0, 2), (0, 3, 4), (1, 3), (2, 4)],
            'F3': [(0, 1), (0, 2), (1, 2, 3), (1, 2, 4), (3, 4)]}
    for name, fam in fams.items():
        choices = [dirs(s, B) for s in fam]
        tot = rk = ok = 0
        for rows in itertools.product(*choices):
            rows = list(rows); tot += 1
            if rank(rows, N) != N - 1:
                continue
            rk += 1
            if cell_ok(rows, N, pts)[0]:
                ok += 1; print('  PASS', name, rows, flush=True)
        print('%s B=%d: instances %d, rank 4: %d, passing Cell: %d' % (name, B, tot, rk, ok), flush=True)


if __name__ == '__main__':
    main()
