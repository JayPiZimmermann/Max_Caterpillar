#!/usr/bin/env python3
"""Can m-th mixed differences separate max_m from the out-star germs at an m-tie?
Out-star germ s_{a,c}(z) = relu(z_c - z_a + sum_{l != a,c} relu(z_l - z_c)) on R^m.
Feature vector of f: (MD_{q,delta} f) over random base points q and steps delta, where
MD = sum_{S subset [m]} (-1)^{m-|S|} f(q + delta 1_S).  MD kills every function independent of
some coordinate, hence linear functions and the auxiliary span.
max_m separated  <=>  max's vector not in span of the out-star vectors (exact rationals, sympy).
Usage: outstar_md.py m npts [family]   family: out (default) | outfaces"""
import sys, itertools, random
from fractions import Fraction
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from pn_test import rank_mod_p

def relu(x): return x if x > 0 else 0

def md(f, q, d, m):
    tot = 0
    for S in itertools.product([0, 1], repeat=m):
        z = [q[i] + d * S[i] for i in range(m)]
        tot += (-1) ** (m - sum(S)) * f(z)
    return tot

def main():
    m, npts = int(sys.argv[1]), int(sys.argv[2])
    fam = sys.argv[3] if len(sys.argv) > 3 else 'out'
    random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 5)
    funcs = []
    for a in range(m):
        for c in range(m):
            if a == c: continue
            leaves = [l for l in range(m) if l not in (a, c)]
            if fam == 'out':
                funcs.append(lambda z, a=a, c=c, L=leaves: relu(z[c] - z[a] + sum(relu(z[l] - z[c]) for l in L)))
            else:
                # faces keeping every leaf edge: linear (+ (z_l - z_c)) or hinge
                for st in itertools.product([0, 1], repeat=len(leaves)):
                    funcs.append(lambda z, a=a, c=c, L=leaves, st=st: relu(z[c] - z[a] + sum(
                        (z[l] - z[c]) if s else relu(z[l] - z[c]) for l, s in zip(L, st))))
    mx = lambda z: max(z)
    pts = []
    for _ in range(npts):
        d = random.randint(5, 200)
        q = [random.randint(-2 * d, d) for _ in range(m)]
        pts.append((q, d))
    A = np.array([[md(f, q, d, m) for f in funcs] for (q, d) in pts], dtype=np.int64)
    b = np.array([[md(mx, q, d, m)] for (q, d) in pts], dtype=np.int64)
    r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, b], axis=1))
    print(f'm={m} family={fam}: {len(funcs)} functions, {npts} MD tests; rank {r1}, with max {r2} -> '
          f'{"SEPARATED" if r2 > r1 else "not separated"}', flush=True)

if __name__ == '__main__':
    main()
