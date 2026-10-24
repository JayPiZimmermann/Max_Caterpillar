"""Thin wrapper around scipy's bundled HiGHS core (avoids linprog's per-call overhead).
lp_status(A, lo, hi, lb, ub, c) -> 'optimal' | 'infeasible' | other, and solution x."""
import numpy as np
from scipy.optimize._highspy import _core as hc

INF = hc.kHighsInf


def solve(c, A, lo, hi, lb, ub):
    h = hc._Highs()
    h.setOptionValue('output_flag', False)
    lp = hc.HighsLp()
    m, n = A.shape
    lp.num_col_ = n; lp.num_row_ = m
    lp.col_cost_ = np.asarray(c, float)
    lp.col_lower_ = np.where(np.isinf(lb), -INF, lb); lp.col_upper_ = np.where(np.isinf(ub), INF, ub)
    lp.row_lower_ = np.where(np.isinf(lo), -INF, lo); lp.row_upper_ = np.where(np.isinf(hi), INF, hi)
    A = np.asarray(A, float)
    # column-wise sparse
    starts, idx, vals = [0], [], []
    for j in range(n):
        nz = np.nonzero(A[:, j])[0]
        idx.extend(nz.tolist()); vals.extend(A[nz, j].tolist()); starts.append(len(idx))
    lp.a_matrix_.format_ = hc.MatrixFormat.kColwise
    lp.a_matrix_.start_ = np.array(starts, dtype=np.int32)
    lp.a_matrix_.index_ = np.array(idx, dtype=np.int32)
    lp.a_matrix_.value_ = np.array(vals, float)
    lp.a_matrix_.num_col_ = n; lp.a_matrix_.num_row_ = m
    h.passModel(lp)
    h.run()
    st = h.getModelStatus()
    name = h.modelStatusToString(st)
    x = np.array(h.getSolution().col_value) if name == 'Optimal' else None
    return name, x, (h.getInfo().objective_function_value if name == 'Optimal' else None)


if __name__ == '__main__':
    import time
    A = np.array([[1., 1.], [1., -1.]])
    t = time.time()
    for _ in range(1000):
        r = solve([0, 0], A, np.array([1., -np.inf]), np.array([np.inf, -2.]), np.array([-np.inf] * 2), np.array([np.inf] * 2))
    print(r, (time.time() - t) / 1000)
    print(solve([0, 0], A, np.array([1., 3.]), np.array([1., 3.]), np.array([0., 0.]), np.array([0.5, 0.5]))[0])
