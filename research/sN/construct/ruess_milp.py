import sys, itertools
from milp_top import milp_top
n = int(sys.argv[1]); k = int(sys.argv[2]); mode = sys.argv[3]; tl = float(sys.argv[4])
E = list(itertools.combinations(range(n), 2))
def forest(es):
    par = list(range(n))
    def f(a):
        while par[a] != a: a = par[a]
        return a
    for a, b in es:
        ra, rb = f(a), f(b)
        if ra == rb: return False
        par[ra] = rb
    return True
F = [es for kk in range(1, k + 1) for es in itertools.combinations(E, kk) if forest(es)]
LW = []; seen = set()
for A in F:
    for B in F:
        if len(A) != len(B) or set(A) & set(B) or (B, A) in seen: continue
        seen.add((A, B)); l = [0] * n; W = {}
        for (i, j) in A: l[j] += 1; W[(i, j)] = W.get((i, j), 0) + 1
        for (i, j) in B: l[j] -= 1; W[(i, j)] = W.get((i, j), 0) - 1
        LW.append((l, W))
print('atoms', len(LW), flush=True)
r = milp_top(n, LW, tlim=tl, exact_mode=(mode == 'exact'))
if r:
    supp, w = r; print('neurons', len(supp))
    for s in supp: print(LW[s], w[s])
