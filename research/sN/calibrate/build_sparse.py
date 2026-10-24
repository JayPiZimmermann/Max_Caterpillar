"""Build the sparse formulation (kink rows + D_S rows) for N without the
rank check (python build_sparse.py N)."""
import sys, time, pickle, numpy as np
from scipy.sparse import csr_matrix, save_npz
from core import units_of
from kinks import kink_groups
from sparse_form import D_S_unit, subsets3
N = int(sys.argv[1])
t0 = time.time()
U = units_of(N)
print('units', len(U), time.time() - t0, flush=True)
groups, per_unit = kink_groups(N, U)
gkeys = list(groups)
print('groups', len(gkeys), time.time() - t0, flush=True)
rows, cols, vals = [], [], []
for r, g in enumerate(gkeys):
    for u, lam in groups[g].items():
        rows.append(r); cols.append(u); vals.append(lam)
Kink = csr_matrix((vals, (rows, cols)), shape=(len(gkeys), len(U)), dtype=np.int64)
Ss = subsets3(N)
Dm = np.array([[D_S_unit(S, k) for k in U] for S in Ss], dtype=np.int64)
tD = np.array([(-1) ** (len(S) + 1) for S in Ss], dtype=np.int64)
print('D rows done', time.time() - t0, flush=True)
save_npz(f'data/kink_csr_{N}.npz', Kink)
np.savez_compressed(f'data/Drows_{N}.npz', Dm=Dm, tD=tD)
pickle.dump((U, gkeys, Ss), open(f'data/sparse_meta_{N}.pkl', 'wb'))
print('saved', time.time() - t0, flush=True)
