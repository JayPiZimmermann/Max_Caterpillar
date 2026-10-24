#!/usr/bin/env python3
"""Combinatorial companion: the 'strong pass' predicate SP(k,L) := (all digits
c_o = 0) and M(T) != {}, which the exact Lambda runs show is implied by
Lambda_L U_k != 0. For every key of dictionary(N): count SP localities, the
SP triples, check T = {apex} u e with e in M, and |Neg| = 1 on SP localities
(so cubic Cases II/III contribute nothing).  Usage: python3 strong_pass.py N
"""
import itertools, math, sys, collections
sys.path.insert(0, 'scripts')
from vocabulary_search import dictionary
N = int(sys.argv[1]); K0, _ = dictionary(N)
f = math.factorial(N - 3)
mx = 0; mxT = 0; bad_shape = 0; neg_hist = collections.Counter(); hist = collections.Counter()
for h, M in K0:
    kap = [h[o] + sum(1 for i, j in M if i == o) for o in range(N)]
    touched = {x for e in M for x in e}
    apexes = {o for o in range(N) if h[o] == -1 and o not in touched}
    neg = {o for o in range(N) if kap[o] < 0}
    cnt = 0; Ts = set()
    for T in itertools.combinations(range(N), 3):
        MT = [e for e in M if e[0] in T and e[1] in T]
        if not MT: continue
        out = [o for o in range(N) if o not in T]
        for perm in itertools.permutations(range(1, N - 2)):
            rho = dict(zip(out, perm)); ok = True
            for o in out:
                nb = [j if i == o else i for i, j in M if o in (i, j)]
                if kap[o] - sum(1 for u in nb if u in T or rho[u] < rho[o]): ok = False; break
            if ok:
                cnt += 1; Ts.add(T); neg_hist[len(neg)] += 1
                if not (len(MT) == 1 and set(T) - set(MT[0]) <= apexes): bad_shape += 1
    hist[cnt] += 1; mx = max(mx, cnt); mxT = max(mxT, len(Ts))
print(f'N={N} keys={len(K0)} max SP localities/key={mx} (={mx/f} x (N-3)!), '
      f'(N-2)(N-3)!={(N-2)*f}, 2(N-3)!={2*f}; max SP triples/key={mxT}; '
      f'SP localities not of form apex+edge: {bad_shape}; |Neg| on SP localities: {dict(neg_hist)}')
print('  histogram', sorted(hist.items()))
