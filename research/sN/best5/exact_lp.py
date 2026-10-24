"""Feasibility of  {x in R^n : c0 + c.x = 0 (rows of E),  c0 + c.x >= 0 (rows of I)}  with an
answer that is EXACT in the direction used by exclusion proofs:
 - 'feasible' is accepted from the floating LP (conservative: a search only explores more);
 - 'infeasible' is returned only with an exactly verified Farkas certificate
   (y free, z >= 0 with sum y_i c_i + sum z_j c_j = 0 and -sum y_i c0_i - sum z_j c0_j = 1),
   reconstructed on the float support by exact Gaussian elimination over Fractions;
   if that fails, exact Fourier-Motzkin decides.
STATS = [calls, float-feasible, certified-infeasible, FM fallbacks]."""
import numpy as np
from fractions import Fraction as Fr
import fastlp

STATS = [0, 0, 0, 0]


def solve_eq(E, n):
    """E rows [c0, c1..cn] meaning c0 + c.x = 0; returns a particular solution or None."""
    M = [list(r[1:]) + [-r[0]] for r in E]; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; inv = 1 / M[r][c]; M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    if any(row[n] != 0 for row in M[r:]):
        return None
    x0 = [Fr(0)] * n
    for row, pc in zip(M[:r], piv): x0[pc] = row[n]
    return x0


def _fm(E, I, n):
    from k2_exact import feasible_fm
    return feasible_fm(E, I, n)


def feasible(E, I, n):
    STATS[0] += 1
    if n == 0:
        return all(r[0] == 0 for r in E) and all(r[0] >= 0 for r in I)
    rows = E + I
    A = np.array([[float(c) for c in r[1:]] for r in rows]) if rows else np.zeros((0, n))
    c0 = np.array([float(r[0]) for r in rows])
    lo = -c0.copy(); hi = np.full(len(rows), np.inf); hi[:len(E)] = -c0[:len(E)]
    name, x, _ = fastlp.solve(np.zeros(n), A, lo, hi, np.full(n, -np.inf), np.full(n, np.inf))
    if name == 'Optimal':
        STATS[1] += 1; return True
    if name == 'Infeasible':
        m1, m = len(E), len(rows)
        # Farkas LP in variables u = (y, z): sum u_i c_i = 0 (n rows), -sum u_i c0_i = 1
        B = np.zeros((n + 1, m)); B[:n, :] = A.T; B[n, :] = -c0
        lb = np.full(m, -np.inf); lb[m1:] = 0
        nm, u, _ = fastlp.solve(np.zeros(m), B, np.r_[np.zeros(n), 1.], np.r_[np.zeros(n), 1.], lb, np.full(m, np.inf))
        if nm == 'Optimal':
            supp = [i for i in range(m) if abs(u[i]) > 1e-10]
            # exact: unknowns u_supp; equations sum_i u_i c_i[t] = 0, -sum u_i c0_i = 1
            Erows = [[Fr(0)] + [-rows[i][1 + t] for i in supp] for t in range(n)]
            Erows.append([Fr(1)] + [rows[i][0] for i in supp])   # 1 + sum u c0 = 0
            sol = solve_eq(Erows, len(supp))
            if sol is not None and all(sol[k] >= 0 for k, i in enumerate(supp) if i >= m1):
                STATS[2] += 1; return False
            # retry: round float multipliers and verify directly
            ur = [Fr(u[i]).limit_denominator(10 ** 6) for i in supp]
            if all(ur[k] >= 0 for k, i in enumerate(supp) if i >= m1) and \
               all(sum(ur[k] * rows[i][1 + t] for k, i in enumerate(supp)) == 0 for t in range(n)) and \
               -sum(ur[k] * rows[i][0] for k, i in enumerate(supp)) > 0:
                STATS[2] += 1; return False
    STATS[3] += 1
    return _fm(E, I, n)
