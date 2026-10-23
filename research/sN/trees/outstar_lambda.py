#!/usr/bin/env python3
"""Exact check of the explicit functional killing all out-star germs at an m-tie:
Lambda f = sum_t MD_{delta^(t)} f - (m-1) MD_{1} f, delta^(t) = all ones except D = m-2 at t,
MD_delta f = sum_S (-1)^{m-|S|} f(delta_S).  Claims: Lambda(max) = (-1)^(m-1), Lambda(s_ac) = 0."""
import itertools
def relu(x): return x if x > 0 else 0
for m in range(4, 12):
    subsets = list(itertools.product([0, 1], repeat=m))
    md = lambda f, d: sum((-1) ** (m - sum(S)) * f([d[i] * S[i] for i in range(m)]) for S in subsets)
    D = m - 2
    def lam(f):
        tot = -(m - 1) * md(f, [1] * m)
        for t in range(m):
            d = [1] * m; d[t] = D
            tot += md(f, d)
        return tot
    vals = set()
    for a in range(m):
        for c in range(m):
            if a != c:
                L = [l for l in range(m) if l not in (a, c)]
                vals.add(lam(lambda z: relu(z[c] - z[a] + sum(relu(z[l] - z[c]) for l in L))))
    print(f'm={m}: Lambda(max) = {lam(max)}, Lambda(out-stars) in {sorted(vals)}', flush=True)
