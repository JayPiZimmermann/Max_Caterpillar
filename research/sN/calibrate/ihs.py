"""Implicit hitting set search for s_N (mod-P search; lower bounds certified
separately by certify.py).

Loop: K = minimum hitting set of the current cut family (HiGHS MILP);
if K spans max modulo aux (mod P) we are done (|K| = s_N candidate, exact
certification via Space.exact); otherwise compute `reps` hyperplane cuts
disjoint from K (order: K first, then a random order of the rest) and add
their S_N-orbits.  State is saved after every iteration (resumable).
usage: python ihs.py N max_iters seed [milp_time_limit] [reps]
"""
import sys, time, pickle, os
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix
from modp import Space
from cuts import hyperplane_cut, orbit
from core import unit_perm_table

N, iters, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600
reps = int(sys.argv[5]) if len(sys.argv) > 5 else 2
sp = Space(N)
perms, T = unit_perm_table(N, sp.U)
rng = np.random.default_rng(seed)
state_file = f'data/ihs_{N}_{seed}.pkl'
cuts, base = set(), []
if os.path.exists(state_file):
    cuts, base = pickle.load(open(state_file, 'rb'))
    print('resumed', len(cuts), 'cuts', flush=True)


def solve_hs(cuts, n):
    cl = list(cuts)
    rows = np.repeat(np.arange(len(cl)), [len(c) for c in cl])
    cols = np.fromiter((u for c in cl for u in c), dtype=np.int64)
    A = csr_matrix((np.ones(len(cols)), (rows, cols)), shape=(len(cl), n))
    res = milp(np.ones(n), constraints=LinearConstraint(A, lb=1, ub=np.inf),
               integrality=np.ones(n), bounds=Bounds(0, 1),
               options={'time_limit': tl, 'disp': False})
    K = [int(i) for i in np.nonzero(res.x > 0.5)[0]]
    return K, res


t0 = time.time()
for it in range(iters):
    if cuts:
        K, res = solve_hs(cuts, sp.n)
        lb, st = getattr(res, 'mip_dual_bound', None), res.status
    else:
        K, lb, st = [], 0, None
    feas = sp.feasible(K) if K else False
    print(f'it {it}: cuts {len(cuts)} |K| {len(K)} dual_bound {lb} status {st} feasible {feas} t={time.time()-t0:.0f}s', flush=True)
    if feas:
        print('OPTIMUM candidate', K, flush=True)
        pickle.dump(K, open(f'data/ihs_opt_{N}_{seed}.pkl', 'wb'))
        break
    Kset = set(K)
    for rep in range(reps):
        rest = [int(u) for u in rng.permutation(sp.n) if u not in Kset]
        basis, cut = hyperplane_cut(sp.G, sp.t, K + rest)
        assert not (set(cut.tolist()) & Kset)
        base.append(frozenset(int(u) for u in cut))
        ob = orbit(cut, T)
        cuts |= ob
        print(f'   cut size {len(cut)}, orbit {len(ob)}', flush=True)
    pickle.dump((cuts, base), open(state_file, 'wb'))
