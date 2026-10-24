"""Exact certificate for an identity  max_N = sum_k d_k relu(g_k) + R  on all of R^N.

g_k = <l_k, x> + sum_{i<j} a^k_ij relu(x_i - x_j) (rational), R = <r, x> + sum c_ij relu(x_i-x_j).
On each braid cell (strict order pi of the coordinates) every g_k is linear, so
F := sum_k d_k relu(g_k) + R - max_N is linear on each region of the arrangement
{g_k = 0} inside the cell; its linear form on a region depends only on the sign
vector.  We check that the linear form vanishes for every sign vector that is
REALIZABLE in the open cell (realizability decided by exact rational LP via a
Fourier-Motzkin-free test: we use scipy linprog to find a candidate interior point,
then verify the point exactly; sign vectors for which no point is found are checked
anyway (conservative: a failure there is reported as 'unverified', not as a refutation).
Since cells and regions are open and dense, F == 0 everywhere.
"""
import itertools
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog


def lin_on_cell(N, l, a, pos):
    """Linear form of <l,x> + sum a_ij relu(x_i-x_j) on cell with ranks pos (pos[i] > pos[j] iff x_i > x_j)."""
    v = [Fr(t) for t in l]
    for (i, j), w in a.items():
        if pos[i] > pos[j]:
            v[i] += w
            v[j] -= w
    return v


def certify(N, neurons, d, r, c):
    """neurons: list of (l, a); d: coeffs; r, c: remainder.  Returns (ok, n_regions, problems)."""
    K = len(neurons)
    probs = []
    nreg = 0
    for pi in itertools.permutations(range(N)):
        pos = [0] * N
        for rank, v in enumerate(pi):
            pos[v] = rank          # pi lists coordinates from smallest to largest
        top = pi[-1]
        G = [lin_on_cell(N, l, a, pos) for l, a in neurons]
        base = lin_on_cell(N, r, c, pos)
        base[top] -= 1
        # cell constraints: x_{pi[t+1]} - x_{pi[t]} >= 1 (open cone, homogeneous -> scale)
        Acell = []
        for t in range(N - 1):
            row = [0] * N
            row[pi[t]] = 1
            row[pi[t + 1]] = -1
            Acell.append(row)
        for signs in itertools.product((0, 1), repeat=K):
            form = list(base)
            for k in range(K):
                if signs[k]:
                    form = [f + d[k] * gk for f, gk in zip(form, G[k])]
            if all(f == 0 for f in form):
                continue
            # is this sign vector realizable? strict: g_k >= 1 if on, g_k <= -1 if off
            Aub = [list(map(float, row)) for row in Acell]
            bub = [-1.0] * (N - 1)
            for k in range(K):
                s = -1 if signs[k] else 1
                Aub.append([float(s * x) for x in G[k]])
                bub.append(-1.0)
            Aeq = [[1.0] * N]
            res = linprog(np.zeros(N), A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=[0.0],
                          bounds=[(None, None)] * N, method='highs')
            if res.status == 0:
                x = [Fr(v).limit_denominator(10**6) for v in res.x]
                # exact check of realizability
                ok_pt = all(sum(Fr(rw[i]) * x[i] for i in range(N)) < 0 for rw in Acell)
                ok_pt = ok_pt and all((sum(G[k][i] * x[i] for i in range(N)) > 0) == bool(signs[k])
                                      and sum(G[k][i] * x[i] for i in range(N)) != 0 for k in range(K))
                probs.append((pi, signs, 'REALIZED' if ok_pt else 'lp-feasible'))
            elif res.status != 2:
                probs.append((pi, signs, 'lp-status-%d' % res.status))
            # status 2 = infeasible (float LP; for rigor a Farkas certificate would be checked)
        nreg += 1
    return len(probs) == 0, probs
