"""EXACT necessary-condition check (Cell condition, PROOFS.md Lemma C) for first layers with |J+| = 1.

If a zero-bias two-hidden-layer net computes max_N and has exactly one first-layer row with
positive coordinate sum, then (translation to +infinity) max_N = l + F(relu(r_1.x), ..., relu(r_m.x))
for the translation-invariant rows r_j (J0) and a linear l.  Hence on every open cell K of the
J0 arrangement, with active set A(K) = {j : r_j.x > 0 on K}, and every braid region B_a meeting K:
        e_a - l  lies in  span{ r_j : j in A(K) }.                                  (Cell)
This script restricts to J0 consisting of oriented root rows e_i - e_j, enumerates all families
of m such rows (all orientations), keeps those satisfying C3 (every 3-set contains a support),
C4 (every coordinate lies in a support) and rank N-1, and decides (Cell) exactly: cells are found
from exact integer sample points (each sample is a genuine witness of a nonempty cell, so an
infeasible system is a PROOF of failure; a feasible system on samples is only 'not excluded').
Usage: python cellcond.py N m [samples] [seed]"""
import sys, itertools, random
from fractions import Fraction as Fr


def rref_consistent(rows):
    """rows: list of (coeffs list, rhs). exact consistency of the linear system."""
    M = [list(map(Fr, c)) + [Fr(r)] for c, r in rows]
    if not M:
        return True
    n = len(M[0]) - 1
    piv_row = 0
    for col in range(n):
        p = next((i for i in range(piv_row, len(M)) if M[i][col] != 0), None)
        if p is None:
            continue
        M[piv_row], M[p] = M[p], M[piv_row]
        pv = M[piv_row][col]
        M[piv_row] = [v / pv for v in M[piv_row]]
        for i in range(len(M)):
            if i != piv_row and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[piv_row])]
        piv_row += 1
    return all(any(v != 0 for v in r[:-1]) or r[-1] == 0 for r in M)


def nullspace(R, N):
    """basis of {w in Q^N : r.w = 0 for r in R}"""
    M = [list(map(Fr, r)) for r in R]
    pivots, piv_row = [], 0
    for col in range(N):
        p = next((i for i in range(piv_row, len(M)) if M[i][col] != 0), None)
        if p is None:
            continue
        M[piv_row], M[p] = M[p], M[piv_row]
        pv = M[piv_row][col]
        M[piv_row] = [v / pv for v in M[piv_row]]
        for i in range(len(M)):
            if i != piv_row and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[piv_row])]
        pivots.append(col); piv_row += 1
    free = [c for c in range(N) if c not in pivots]
    basis = []
    for f in free:
        w = [Fr(0)] * N; w[f] = Fr(1)
        for i, pc in enumerate(pivots):
            w[pc] = -M[i][f]
        basis.append(w)
    return basis


def rank(R, N):
    return N - len(nullspace(R, N)) if R else 0


def cell_ok(rows, N, pts):
    seen = set()
    for x in pts:
        A = tuple(j for j, r in enumerate(rows) if sum(c * v for c, v in zip(r, x)) > 0)
        a = max(range(N), key=lambda i: x[i])
        seen.add((A, a))
    cons = []
    for A, a in seen:
        for w in nullspace([rows[j] for j in A], N):
            # (e_a - l).w = 0  <=>  l.w = w_a
            cons.append((w, w[a]))
    return rref_consistent(cons), len(seen)


def main():
    N, m = int(sys.argv[1]), int(sys.argv[2])
    S = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    pts = [rng.sample(range(-10**6, 10**6), N) for _ in range(S)]
    pairs = list(itertools.combinations(range(N), 2))
    total = passC = passCell = 0
    survivors = []
    for fam in itertools.combinations(pairs, m):
        sup = [set(p) for p in fam]
        if not all(any(s <= set(T) for s in sup) for T in itertools.combinations(range(N), 3)):
            continue
        if N >= 4 and not all(any(i in s for s in sup) for i in range(N)):
            continue
        for orient in itertools.product((1, -1), repeat=m):
            rows = []
            for (i, j), o in zip(fam, orient):
                r = [0] * N; r[i] = o; r[j] = -o; rows.append(r)
            total += 1
            if rank(rows, N) != N - 1:
                continue
            passC += 1
            ok, ncells = cell_ok(rows, N, pts)
            if ok:
                passCell += 1; survivors.append((fam, orient))
    print('N %d m %d: oriented families %d, with C3+C4+rank %d, passing Cell on samples %d'
          % (N, m, total, passC, passCell))
    for s in survivors[:20]:
        print('  survivor', s)


if __name__ == '__main__':
    main()
