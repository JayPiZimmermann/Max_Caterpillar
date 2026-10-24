"""Ranks (mod-p lower bounds) of the evaluation matrix for N given."""
import sys, time
import numpy as np, flint
from core import *
N = int(sys.argv[1]); npts = int(sys.argv[2])
t0 = time.time()
U = units_of(N); print('units', len(U), time.time()-t0)
pts = random_points(N, npts, 1)
EU = eval_units_matrix(U, pts); EA = eval_aux_matrix(N, pts); Em = eval_max(pts)
def rk(A):
    A = np.asarray(A) % P
    return flint.nmod_mat(A.shape[0], A.shape[1], [int(v) for v in A.ravel()], P).rank()
print('rank aux', rk(EA))
print('rank units+aux', rk(np.hstack([EU, EA])))
print('rank units+aux+max', rk(np.hstack([EU, EA, Em[:, None]])))
print('time', time.time()-t0)
