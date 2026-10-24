"""N!/6 candidate: for each 3-set T={a<m<M} and order rho of the rest, unit
u_{T,rho} = (apex a, path rho.m.M), detector Lambda_{T,rho} (third mixed
difference in x_a,x_m,x_M at z: z_T = top, z_{rho_j} = j). Check the square
matrix: rank, diagonal, and whether 'd_{u'} sees u' is acyclic (triangular)."""
import itertools, sys, numpy as np
from rank import rank_mod
from lam import unit

def lamT(N, T, rho, f):
    z = [0] * N
    for j, l in enumerate(rho): z[l] = 4 * (j + 1)
    for t in T: z[t] = 4 * (N - 2)
    tot = 0
    for e in itertools.product((0, 1), repeat=3):
        x = z[:]
        for t, ei in zip(T, e): x[t] += ei
        tot += (-1) ** sum(e) * f(x)
    return tot

N = int(sys.argv[1])
idx = []
for T in itertools.combinations(range(N), 3):
    rest = [i for i in range(N) if i not in T]
    for rho in itertools.permutations(rest):
        idx.append((T, list(rho)))
M = np.array([[lamT(N, T, rho, lambda x, T2=T2, r2=r2: unit(T2[0], r2 + [T2[1], T2[2]], x))
               for (T2, r2) in idx] for (T, rho) in idx], dtype=np.int64)
print("N", N, "size", len(idx), "rank", rank_mod(M), "diag values", set(np.diag(M).tolist()),
      "offdiag nonzeros", int((M != 0).sum() - (np.diag(M) != 0).sum()))
# acyclicity of off-diagonal support
n = len(idx); adj = [[j for j in range(n) if j != i and M[i, j] != 0] for i in range(n)]
state = [0] * n; cyc = False
sys.setrecursionlimit(100000)
def dfs(i):
    global cyc
    state[i] = 1
    for j in adj[i]:
        if state[j] == 1: cyc = True
        elif state[j] == 0: dfs(j)
    state[i] = 2
for i in range(n):
    if state[i] == 0: dfs(i)
print(" off-diagonal support acyclic (triangularizable):", not cyc)
