"""MILP: min #neurons with braid-PL sum and top = 1 (dictionary given as (l,W) list)."""
import numpy as np, time
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import coo_matrix, vstack, hstack, identity, csr_matrix
from nonsym import rows_for, top_coef
def milp_top(n, LW, M=50.0, tlim=1800, verbose=True, exact_mode=False):
    m = len(LW)
    if exact_mode:
        from nonsym import exact_rows
        eqs, nv = exact_rows(n, LW)
        I = [i for i, (d, r) in enumerate(eqs) for _ in d]; J = [k for d, r in eqs for k in d]; V = [float(c) for d, r in eqs for c in d.values()]
        A = coo_matrix((V, (I, J)), shape=(len(eqs), nv)).tocsr(); b = np.array([float(r) for d, r in eqs])
    else:
        rows = rows_for(n, LW); R = list(rows.values())
        T = [float(top_coef(n, l, W)) for l, W in LW]
        I = [i for i, e in enumerate(R) for _ in e] + [len(R)] * m; J = [k for e in R for k in e] + list(range(m))
        V = [float(c) for e in R for c in e.values()] + T
        A = coo_matrix((V, (I, J)), shape=(len(R) + 1, m)).tocsr(); b = np.zeros(len(R) + 1); b[-1] = 1; nv = m
    # vars: w (nv), z (m binary)
    c = np.concatenate([np.zeros(nv), np.ones(m)])
    Aeq = hstack([A, csr_matrix((A.shape[0], m))])
    Im = identity(nv, format='csr')[:m]
    Zm = identity(m, format='csr') * M
    up = hstack([Im, -Zm]); lo = hstack([Im, Zm])
    cons = [LinearConstraint(Aeq, b, b), LinearConstraint(up, -np.inf, 0), LinearConstraint(lo, 0, np.inf)]
    integ = np.concatenate([np.zeros(nv), np.ones(m)])
    bounds = Bounds(np.concatenate([-M * np.ones(nv), np.zeros(m)]), np.concatenate([M * np.ones(nv), np.ones(m)]))
    t0 = time.time()
    res = milp(c, constraints=cons, integrality=integ, bounds=bounds, options={'time_limit': tlim, 'disp': False})
    if verbose: print('status', res.status, res.message, 'obj', res.fun, 'bound', getattr(res, 'mip_dual_bound', None), '%.0fs' % (time.time() - t0), flush=True)
    if res.x is None: return None
    w = res.x[:nv]; supp = [k for k in range(m) if abs(w[k]) > 1e-7]
    return supp, w
