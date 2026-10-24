#!/usr/bin/env python3
"""Direct exact check of the m-locality functional on the normalized dictionary
(research/sN/polytope/direct.py), independent of the tree-form model.
Psi_L(f) = sum_{eps in {0,1}^T} (-1)^{m-|eps|} f(p + eps), p_T = 0,
p_o = -K B^{rho(o)} (integers).  Checks Psi(max) != 0, Psi(aux) = 0 for all L,
and for every unit k: passes(k) := #{L : Psi_L(U_k) != 0} <= 4^m (N-m)!.
Usage: direct.py N m"""
import itertools, math, sys
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs

N, m = int(sys.argv[1]), int(sys.argv[2])
K, B = 10 ** 4, 64
K0, _ = vs.dictionary(N)
units = sorted(k for k in K0 if not vs.is_auxiliary(k))
aux = vs.aux_functions(N)
cubes = [(e, (-1) ** (m - sum(e))) for e in itertools.product((0, 1), repeat=m)]
pas = {k: 0 for k in units}
nL = 0
for T in itertools.combinations(range(N), m):
    rest = [o for o in range(N) if o not in T]
    for order in itertools.permutations(rest):
        nL += 1
        p = [0] * N
        for k_, o in enumerate(order):
            p[o] = -K * B ** (k_ + 1)
        pts = []
        for e, s in cubes:
            x = list(p)
            for t, et in zip(T, e):
                x[t] += et
            pts.append((x, s))
        assert sum(s * max(x) for x, s in pts) != 0
        for a in aux:
            assert sum(s * vs.eval_aux(a, x) for x, s in pts) == 0
        for k in units:
            if sum(s * vs.eval_key(k, x) for x, s in pts) != 0:
                pas[k] += 1
mx = max(pas.values())
f = math.factorial(N - m)
print(f'N={N} m={m}: localities {nL}, units {len(units)}, max passes {mx} = {mx/f} (N-m)!, '
      f'4^m bound {4**m}: {"OK" if mx <= 4**m * f else "FAIL"}; implied s_N >= {math.comb(N,m)*f/mx:.3f}')
