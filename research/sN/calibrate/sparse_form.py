"""Sparse exact formulation of the expansion problem.

Rows (linear functionals on the span of units, auxiliary functions and max_N):
  KINK_(pi,d): kink coefficient along d.x = 0 inside the braid cell pi
               (kills max_N and every translation-invariant auxiliary combination);
  D_S, S subset [N], |S| >= 3: mixed difference at 0 over the coordinates of S,
               D_S f = sum_{R subset S} (-1)^{|S|-|R|} f(1_R)
               (kills all auxiliary functions; D_S max_N = (-1)^{|S|+1}).
Necessary condition for an expansion max_N = sum_{k in K} d_k U_k + R:
  KINK d = 0 and D_S d = D_S max_N for all S.   (Valid as stated: R may be taken
  translation-invariant + linear, see NOTE in calibrate/README.)
"""
import itertools
import numpy as np
from kinks import kink_groups


def D_S_unit(S, key):
    h, M = key
    tot = 0
    for r in range(len(S) + 1):
        for R in itertools.combinations(S, r):
            s = set(R)
            a = sum(h[i] for i in R) + sum(1 for i, j in M if i in s and j not in s)
            tot += (-1) ** (len(S) - r) * max(a, 0)
    return tot


def subsets3(N):
    return [S for r in range(3, N + 1) for S in itertools.combinations(range(N), r)]


def build(N, U):
    groups, per_unit = kink_groups(N, U)
    gkeys = list(groups)
    Kink = np.zeros((len(gkeys), len(U)), dtype=np.int64)
    for r, g in enumerate(gkeys):
        for u, lam in groups[g].items():
            Kink[r, u] = lam
    Ss = subsets3(N)
    Dm = np.array([[D_S_unit(S, k) for k in U] for S in Ss], dtype=np.int64)
    target_D = np.array([(-1) ** (len(S) + 1) for S in Ss], dtype=np.int64)
    return gkeys, Kink, Ss, Dm, target_D
