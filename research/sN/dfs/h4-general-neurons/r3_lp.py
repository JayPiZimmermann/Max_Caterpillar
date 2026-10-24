"""Round 3.  MEASURED sparse expansions of max_N in the dictionary of 'atoms'
    max(m_P + m_Q, m_R + m_S),   m_{ii} = x_i, m_{ij} = max(x_i, x_j),
(each atom = (m_R+m_S) + relu(m_P+m_Q-m_R-m_S) is ONE general second-layer neuron over
the pair features; the Wang-Basu k=2 atoms).  Optionally degree-3 sums (deg=3, sampled).
Method: iteratively reweighted L1 (HiGHS LP) on random points, remainder
R = sum p_i x_i + sum s_ij relu(x_i-x_j) free.  Output: support (atoms), saved to npz.
A small support is a LEAD; exactness is decided by r3_cert.py (exact, cells).
Usage: python r3_lp.py N npts iters [deg] [seed]
"""
import sys, itertools, time
import numpy as np
from scipy.optimize import linprog

N = int(sys.argv[1]); M = int(sys.argv[2]); iters = int(sys.argv[3])
deg = int(sys.argv[4]) if len(sys.argv) > 4 else 2
seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
rng = np.random.default_rng(seed)
syms = [(i, i) for i in range(N)] + list(itertools.combinations(range(N), 2))
X = rng.standard_normal((M, N))
mval = {s: np.maximum(X[:, s[0]], X[:, s[1]]) for s in syms}
sides = list(itertools.combinations_with_replacement(range(len(syms)), deg))
SV = np.array([sum(mval[syms[i]] for i in sd) for sd in sides])  # side values
atoms, cols, seen = [], [], set()
t0 = time.time()
for a, b in itertools.combinations(range(len(sides)), 2):
    diff = SV[a] - SV[b]
    if diff.min() >= -1e-12 or diff.max() <= 1e-12:
        continue  # max is one side on the sample: in pair span (lead)
    col = np.maximum(SV[a], SV[b])
    key = tuple(np.round(col[:40], 9))
    if key in seen:
        continue
    seen.add(key)
    atoms.append((sides[a], sides[b]))
    cols.append(col)
A = np.array(cols).T
F = np.concatenate([X] + [np.maximum(X[:, i] - X[:, j], 0)[:, None] for i, j in itertools.combinations(range(N), 2)], 1)
y = X.max(1)
na, nf = A.shape[1], F.shape[1]
print('N', N, 'deg', deg, 'atoms', na, 'points', M, '%.0fs' % (time.time() - t0), flush=True)
w = np.ones(na)
best = None
for it in range(iters):
    # variables: d+ (na), d- (na), f (nf free)
    c = np.concatenate([w, w, np.zeros(nf)])
    Aeq = np.concatenate([A, -A, F], 1)
    bounds = [(0, None)] * (2 * na) + [(None, None)] * nf
    res = linprog(c, A_eq=Aeq, b_eq=y, bounds=bounds, method='highs')
    if res.status != 0:
        print('LP status', res.status, res.message); break
    d = res.x[:na] - res.x[na:2 * na]
    supp = np.nonzero(np.abs(d) > 1e-7)[0]
    # refit on support only, check residual
    B = np.concatenate([A[:, supp], F], 1)
    coef, *_ = np.linalg.lstsq(B, y, rcond=None)
    rel = np.linalg.norm(B @ coef - y) / np.linalg.norm(y)
    print('iter', it, 'support', len(supp), 'refit rel %.2e' % rel, '%.0fs' % (time.time() - t0), flush=True)
    if best is None or len(supp) < best[0]:
        best = (len(supp), supp, d)
    w = 1.0 / (np.abs(d) + 1e-3)
supp = best[1]
print('BEST support', best[0])
for i in supp:
    print('  d=%.6f' % best[2][i], [syms[s] for s in atoms[i][0]], '|', [syms[s] for s in atoms[i][1]])
np.savez('r3_lp_N%d_deg%d_s%d.npz' % (N, deg, seed), supp=supp, d=best[2][supp],
         atoms=np.array([list(atoms[i][0]) + list(atoms[i][1]) for i in supp]), syms=np.array(syms))
