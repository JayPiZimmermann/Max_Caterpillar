"""Build and cache the exact evaluation data for N (python setup_space.py N npts).

Saves data/space_N.npz with
  pts   integer points (rows)                         [npts x N]
  EU,EA,Em  exact integer evaluations of units, aux, max at pts
  S     indices of points whose rows are independent mod P (|S| = rank)
  G,t   quotient coordinates mod P: rref of [EA | EU | Em] restricted to the
        rows S, aux pivot rows removed, so a unit set K spans max modulo aux
        (mod P) iff rank G[:,K] == rank [G[:,K] | t].
"""
import sys, time, os, pickle
import numpy as np, flint
from core import *
N = int(sys.argv[1]); npts = int(sys.argv[2])
os.makedirs('data', exist_ok=True)
t0 = time.time()
U = units_of(N)
pts = random_points(N, npts, 1)
EU = eval_units_matrix(U, pts); EA = eval_aux_matrix(N, pts); Em = eval_max(pts)
F = np.hstack([EA, EU, Em[:, None]]) % P
def nm(A):
    A = np.asarray(A) % P
    return flint.nmod_mat(A.shape[0], A.shape[1], [int(v) for v in A.ravel()], P)
# independent rows: rref of F^T
R, rk = nm(F.T).rref()
Rl = np.array([[int(R[i, j]) for j in range(F.shape[0])] for i in range(rk)], dtype=np.int64)
S = [int(np.nonzero(Rl[i])[0][0]) for i in range(rk)]
print('rank', rk, time.time() - t0)
R2, rk2 = nm(F[S]).rref()
A = np.array(R2.tolist(), dtype=np.int64)  # careful: tolist gives nmod
nA = EA.shape[1]
piv = [int(np.nonzero(A[i])[0][0]) for i in range(rk2)]
assert piv[:nA] == list(range(nA)), piv[:nA + 2]
G = A[nA:, nA:nA + len(U)]
t = A[nA:, -1]
print('quotient dim', G.shape, 'rank check', rk2, time.time() - t0)
np.savez_compressed(f'data/space_{N}.npz', pts=np.array(pts), EU=EU, EA=EA, Em=Em, S=np.array(S), G=G, t=t)
pickle.dump(U, open(f'data/units_{N}.pkl', 'wb'))
