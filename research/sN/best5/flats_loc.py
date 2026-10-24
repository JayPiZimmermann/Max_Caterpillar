"""EXACT: vanishing flats of translation-invariant pair neurons on the tie sets.
A neuron g = <l,x> + sum_{i<j} a_ij relu(x_i-x_j), sum l = 0, has ray values v(S) = g(1_S)
= sum_{i in S} l_i + sum_{i in S, j notin S, i<j} a_ij (14-dim space V).
g vanishes identically on the 3-locality cell C_{T,(o1,o2)} iff v(T) = v(T+o1) = 0, and on the
4-tie cell C_{J} iff v(J) = 0.  'Relevant sets' = 3-sets and 4-sets (15).  For every subset Z of
relevant sets we compute the closure (all relevant S with v(S) = 0 on V_Z) and dim V_Z, exactly.
Output: pickle flats_loc.pkl  {closure_bitmask: (dim, basis rows as Fractions)}"""
import itertools, pickle, sys
from fractions import Fraction as Fr
N = 5
PAIRS = list(itertools.combinations(range(N), 2))
REL = [frozenset(c) for r in (3, 4) for c in itertools.combinations(range(N), r)]


def vrow(S):
    return [Fr(1 if i in S else 0) for i in range(N)] + [Fr(1 if (i in S and j not in S) else 0) for i, j in PAIRS]


def nullspace(rows, nv=15):
    M = [list(r) for r in rows]; piv = []; r = 0
    for c in range(nv):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; inv = 1 / M[r][c]; M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    B = []
    for f in [c for c in range(nv) if c not in piv]:
        v = [Fr(0)] * nv; v[f] = Fr(1)
        for row, pc in zip(M[:r], piv): v[pc] = -row[f]
        B.append(v)
    return B


TRANS = [Fr(1)] * N + [Fr(0)] * len(PAIRS)
RROWS = [vrow(S) for S in REL]


def closure(Z):
    B = nullspace([TRANS] + [RROWS[i] for i in range(len(REL)) if Z >> i & 1])
    cl = 0
    for i in range(len(REL)):
        if all(sum(a * b for a, b in zip(RROWS[i], v)) == 0 for v in B):
            cl |= 1 << i
    return cl, B


if __name__ == '__main__':
    flats = {}
    for Z in range(1 << len(REL)):
        cl, B = closure(Z)
        if cl not in flats:
            flats[cl] = (len(B), B)
    pickle.dump({'REL': REL, 'flats': flats}, open('flats_loc.pkl', 'wb'))
    from collections import Counter
    print('flats', len(flats), 'dims', sorted(Counter(v[0] for v in flats.values()).items()))
