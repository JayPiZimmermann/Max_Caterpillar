"""Sandwich construction: an expansion of max_N from top-active braid-linear
combinations E_m (m = 3..N), one copy of E_m on every m-subset S of [N]
(increasing relabelling), coefficients c_S solved top-down (unitriangular).
Verifies: every embedded key is a unit of K_0(N); the final relation
max_N = sum c_S E_S + aux holds exactly on every fine cell
(scripts/vocabulary_search.exact_expansion, independent of kf.py).
usage: python assemble.py N file_E3 file_E4 ... file_EN   (pickles with 'd': key->coef)
"""
import itertools
import pickle
import sys
from fractions import Fraction

from kf import units_of, mobius_row, subsets3
import vocabulary_search as vs

N = int(sys.argv[1])
files = sys.argv[2:]
assert len(files) == N - 2
E = {}
for m, f in zip(range(3, N + 1), files):
    E[m] = {k: Fraction(v) for k, v in pickle.load(open(f, 'rb'))['d'].items()}


def embed(key, S):
    h, M = key
    H = [0] * N
    for i, s in enumerate(S):
        H[s] = h[i]
    return (tuple(H), frozenset((S[a], S[b]) for a, b in M))


UN = set(units_of(N))
Ss = subsets3(N)
pos = {S: i for i, S in enumerate(Ss)}
blocks = {}
for S in Ss:
    blk = {}
    for k, c in E[len(S)].items():
        kk = embed(k, S)
        assert kk in UN, ('embedded key not a unit', kk)
        blk[kk] = blk.get(kk, 0) + c
    blocks[S] = blk


def D(S, key):
    """D_S of unit key (Moebius at the set S)."""
    h, M = key
    tot = 0
    for r in range(len(S) + 1):
        for R in itertools.combinations(S, r):
            Rs = set(R)
            a = sum(h[i] for i in R) + sum(1 for i, j in M if i in Rs and j not in Rs)
            tot += (-1) ** (len(S) - r) * max(a, 0)
    return tot


# block Moebius values
DB = {S: {T: sum(c * D(T, k) for k, c in blocks[S].items()) for T in Ss if set(T) <= set(S)} for S in Ss}
for S in Ss:
    assert DB[S][S] != 0
coef = {}
for S in sorted(Ss, key=len, reverse=True):
    target = Fraction((-1) ** (len(S) + 1))
    acc = sum(coef[S2] * DB[S2][S] for S2 in coef if set(S) <= set(S2))
    coef[S] = (target - acc) / DB[S][S]
d = {}
for S in Ss:
    for k, c in blocks[S].items():
        d[k] = d.get(k, 0) + coef[S] * c
d = {k: v for k, v in d.items() if v != 0}
print('N', N, 'assembled support', len(d), flush=True)
units = sorted(d)
res = vs.exact_expansion(N, units)
print('exact expansion on this support exists (fine-cell certificate):', res is not None)
pickle.dump({'N': N, 'K': units, 'd': d}, open(f'data/assembled_{N}.pkl', 'wb'))
