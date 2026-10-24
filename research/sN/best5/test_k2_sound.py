"""Soundness test of k2_exact.check_pair: take two neurons of the known 4-neuron identity
(d = +1, -1), set the target to their own locality contributions, and check that the exact DFS
finds a solution on their flats (it must)."""
import runpy, itertools
from fractions import Fraction as Fr
import k2_exact as K
s = runpy.run_path('../dfs/h4-general-neurons/r2_spec_N5_k4.py')
def v(l, a, S): return sum(Fr(l[i]) for i in S) + sum(Fr(c) for (i, j), c in a.items() if i in S and j not in S)
for pick in [(0, 1), (2, 3), (0, 2)]:
    ns = [s['NEURONS'][i] for i in pick]
    Zs = []
    for d, l, a in ns:
        Z = 0
        for i, S in enumerate(K.REL):
            if v(l, a, S) == 0: Z |= 1 << i
        Zs.append(Z)
    tgt = [Fr(0)] * len(K.LOCS)
    for (d, l, a), Z in zip(ns, Zs):
        for q, (T, o) in enumerate(K.LOCS):
            if Z >> K.IDX[T] & 1 and Z >> K.IDX[T | {o}] & 1:
                X = sum(max(v(l, a, {t}), 0) for t in T) - sum(max(v(l, a, set(P)), 0) for P in itertools.combinations(T, 2))
                tgt[q] += Fr(d) * X
    K.TARGET[:] = tgt
    assert all(Z in K.F for Z in Zs), 'flat missing'
    res = K.check_pair(Zs[0], Zs[1], {}, [0])
    print('pair', pick, 'd', [n[0] for n in ns], 'solutions found with d patterns', sorted({r[0] for r in res}))
