#!/usr/bin/env python3
"""All 3-unit supports of max_4 expansions (floating rank screen; each hit is
then certified exactly).  Output: data/all_s4_supports.txt"""
import itertools, os
import numpy as np
import fastsys
from system import DATA, vs, certify
S = fastsys.build(4, verbose=False)
units, A = S['units'], S['A'].toarray()
U = len(units)
Ax = A[:, U:-1]; b = -A[:, -1]
Q, R = np.linalg.qr(Ax); Q = Q[:, np.abs(R.diagonal()) > 1e-9]
P = lambda M: M - Q @ (Q.T @ M)
Au = P(A[:, :U]); bb = P(b[:, None]).ravel()
hits = []
for tri in itertools.combinations(range(U), 3):
    C = Au[:, tri]
    x, res, rk, _ = np.linalg.lstsq(C, bb, rcond=None)
    if np.linalg.norm(C @ x - bb) < 1e-8:
        hits.append(tri)
print(len(hits), 'candidate supports')
with open(os.path.join(DATA, 'all_s4_supports.txt'), 'w') as f:
    for tri in hits:
        out = vs.exact_expansion(4, [units[k] for k in tri])
        assert out is not None and certify(4, *out)
        d, e = out
        f.write(' | '.join(f'h={list(units[k][0])} M={sorted(units[k][1])} d={d[units[k]]}' for k in tri) + '\n')
print('all certified')
