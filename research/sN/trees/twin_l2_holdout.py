#!/usr/bin/env python3
"""Held-out check of the L^2 closure probe: fit max on a random half of the sample points using the first
n_R columns (germs with heads <= R), report the relative residual on the other half.
Usage: twin_l2_holdout.py Afile bfile n1,n2,...   (n_R = cumulative column counts printed by twin_l2.py)"""
import sys
import numpy as np
A = np.load(sys.argv[1]); b = np.load(sys.argv[2]); ns = [int(x) for x in sys.argv[3].split(',')]
rng = np.random.default_rng(0)
for rep in range(2):
    perm = rng.permutation(len(b)); tr, te = perm[: len(b) // 2], perm[len(b) // 2:]
    out = []
    for n in ns:
        c, *_ = np.linalg.lstsq(A[tr, :n], b[tr], rcond=1e-10)
        r_tr = np.linalg.norm(b[tr] - A[tr, :n] @ c) / np.linalg.norm(b[tr])
        r_te = np.linalg.norm(b[te] - A[te, :n] @ c) / np.linalg.norm(b[te])
        out.append(f'n={n}: train {r_tr:.2e} test {r_te:.2e}')
    print(f'split {rep}: ' + '; '.join(out), flush=True)
