"""EXACT enumeration for the first-width lower bound (model B, N=5).
Necessary conditions on the supports of the translation-invariant first-layer rows
(J0 = rows a with sum(a) = 0), proved in RESULTS.md (Lemma H1):
 (C3) every 3-subset of [5] contains the support of some J0 row;
 (C4) for every 4-subset I and every a in I, some J0 row S has a in S, S subset of I.
Supports have size >= 2 (sum zero, nonzero).  Prints the minimum family size and all
minimal families up to the S5 action."""
import itertools
N = 5
V = range(N)
subs = [frozenset(c) for r in (2, 3, 4) for c in itertools.combinations(V, r)]
T3 = [frozenset(c) for c in itertools.combinations(V, 3)]
T4 = [frozenset(c) for c in itertools.combinations(V, 4)]

def ok(F):
    if not all(any(S <= T for S in F) for T in T3):
        return False
    return all(any(a in S and S <= I for S in F) for I in T4 for a in I)

def canon(F):
    return min(tuple(sorted(tuple(sorted(p[i] for i in S)) for S in F)) for p in itertools.permutations(V))

for m in range(1, 8):
    sols = {canon(F) for F in itertools.combinations(subs, m) if ok(F)}
    print('size', m, 'families (up to S5):', len(sols))
    if sols:
        for s in sorted(sols):
            print('  ', s)
        break
