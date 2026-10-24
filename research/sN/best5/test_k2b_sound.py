"""Soundness test of k2b.check on pairs of neurons of the known identity (target = their own
locality contributions); the true sign pattern must be reported."""
import runpy, itertools
from fractions import Fraction as Fr
import k2_exact as K, k2b
s = runpy.run_path('../dfs/h4-general-neurons/r2_spec_N5_k4.py')
def v(l, a, S): return sum(Fr(l[i]) for i in S) + sum(Fr(c) for (i, j), c in a.items() if i in S and j not in S)
for pick in [(0, 1), (2, 3), (0, 2), (1, 3)]:
    ns = [s['NEURONS'][i] for i in pick]; Zs = []
    for d, l, a in ns:
        Zs.append(sum(1 << i for i, S in enumerate(K.REL) if v(l, a, S) == 0))
    tgt = [Fr(0)] * len(K.LOCS)
    for (d, l, a), Z in zip(ns, Zs):
        for q, (T, o) in enumerate(K.LOCS):
            if Z >> K.IDX[T] & 1 and Z >> K.IDX[T | {o}] & 1:
                X = sum(max(v(l, a, {t}), 0) for t in T) - sum(max(v(l, a, set(P)), 0) for P in itertools.combinations(T, 2))
                tgt[q] += (1 if d > 0 else -1) * abs(Fr(d)) * X
    K.TARGET[:] = tgt; k2b.TARGET = K.TARGET; k2b.SINGLE_CACHE.clear()
    # uncovered localities have target 0: drop the 'must be covered' rule for the test
    r = k2b.check(Zs, [0])
    print('pair', pick, 'true d signs', [1 if n[0] > 0 else -1 for n in ns], 'found', r, flush=True)
