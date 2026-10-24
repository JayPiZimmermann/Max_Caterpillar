import sys, itertools
import numpy as np
from nonsym import solve_sparse
n = int(sys.argv[1]); MUS = [1, 2]
want = None
neurons = []; tkeys = []
for c in range(n):
    others = [o for o in range(n) if o != c]
    pairs = list(itertools.combinations(others, 2))
    shapes = [(0, None, None)] + [(mu, P, Q) for mu in MUS for P in pairs for Q in pairs if P != Q]
    for mu, P, Q in shapes:
        for svals in itertools.product((-1, 0, 1), repeat=n - 1):
            s = dict(zip(others, svals))
            if mu == 0: t = ('star', tuple(sorted(s.values())))
            else:
                sh = set(P) & set(Q)
                t = (mu, tuple(sorted(s[v] for v in P if v not in sh)), tuple(sorted(s[v] for v in Q if v not in sh)),
                     tuple(s[v] for v in sh), tuple(sorted(s[v] for v in others if v not in P and v not in Q)))
            neurons.append((mu, P, Q, c, s)); tkeys.append(t)
import ast
keep = set(ast.literal_eval(l.split(' -1/')[0].split(' 1/')[0]) for l in open(sys.argv[2]) if l.startswith('('))
sel = [i for i, t in enumerate(tkeys) if t in keep]
print('types kept', len(keep), 'neurons', len(sel), flush=True)
def toLW(mu, P, Q, c, s):
    l = [0] * n; W = {}
    if mu:
        a, b = P; l[b] += mu; W[(a, b)] = W.get((a, b), 0) + mu       # m_P = x_b + sigma(x_a - x_b)
        a, b = Q; l[b] -= mu; W[(a, b)] = W.get((a, b), 0) - mu
    for o, v in s.items():
        if v: W[(o, c)] = W.get((o, c), 0) + v
    return l, W
LW = [toLW(*neurons[i]) for i in sel]
best, rows, T = solve_sparse(n, LW)
supp, x = best
print('best support', len(supp))
for k in supp: print(neurons[sel[k]], tkeys[sel[k]], x[k])
