"""Exact minimum size of a family F of supports (subsets of [N], size 2..4) with
(C4) for every 4-set I and a in I some S in F with a in S subset I, optionally (C3)
every 3-set contains some S in F. ILP via scipy.optimize.milp (HiGHS)."""
import sys, itertools, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
def solve(N, c3):
    sets = [frozenset(s) for k in (2,3,4) for s in itertools.combinations(range(N), k)]
    idx = {s:i for i,s in enumerate(sets)}
    rows = []
    for I in itertools.combinations(range(N), 4):
        I = frozenset(I)
        for a in I:
            rows.append([idx[s] for s in sets if a in s and s <= I])
    if c3:
        for I in itertools.combinations(range(N), 3):
            rows.append([idx[s] for s in sets if s <= frozenset(I)])
    A = np.zeros((len(rows), len(sets)))
    for r, cols in enumerate(rows): A[r, cols] = 1
    res = milp(np.ones(len(sets)), constraints=LinearConstraint(A, 1, np.inf),
               integrality=np.ones(len(sets)), bounds=Bounds(0, 1),
               options={"time_limit": 600})
    return res.fun, res.status
for N in range(4, int(sys.argv[1]) + 1):
    f4, s4 = solve(N, False); f34, s34 = solve(N, True)
    print(N, "C4:", f4, s4, " C3+C4:", f34, s34, " bound N(2N-9)/4:", N*(2*N-9)/4,
          " C(N,2):", N*(N-1)//2, flush=True)
