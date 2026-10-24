"""Batched float search for the fewest units u with sum d_u M(u) = M(max) (mixed differences),
followed by an exact mod-p confirmation of each hit.  Samples are concentrated near the
diagonal so that M(max) is nonzero on many rows.
Usage: python tau_fast.py k nsamples seed maxsize
"""
import sys, itertools
import numpy as np
from mixed import *

k, m, seed, maxsize = map(int, sys.argv[1:5])
keys = load_keys(k)
rng = np.random.default_rng(seed)
Y = rng.integers(-6, 7, size=(m, k)) + rng.integers(-1000, 1000, size=(m, 1))
D = rng.integers(1, 12, size=(m, k)) * rng.choice([-1, 1], size=(m, k))
Mu = mixed_rows(lambda X: eval_keys(keys, X), Y, D)
Mmax = mixed_rows(lambda X: X.max(axis=1)[:, None], Y, D)[:, 0]
full = [c for c in range(len(keys)) if np.any(Mu[:, c])]
seen = {}
for c in full:
    v = Mu[:, c]
    nz = np.nonzero(v)[0][0]
    g = np.gcd.reduce(np.abs(v))
    seen.setdefault((v // g * (1 if v[nz] > 0 else -1)).tobytes(), c)
reps = list(seen.values())
r = rank_modp(Mu[:, reps])
print('k', k, 'samples', m, 'max-nonzero rows', int(np.count_nonzero(Mmax)), 'rank', r,
      'in span', rank_modp(np.column_stack([Mu[:, reps], Mmax])) == r, 'directions', len(reps), flush=True)
# orthonormal basis of column space (float) to shrink rows
A = Mu[:, reps].astype(float)
U, s, Vt = np.linalg.svd(np.column_stack([A, Mmax]), full_matrices=False)
B = U[:, : r]
Ar = B.T @ A
br = B.T @ Mmax
for size in range(1, maxsize + 1):
    hits = []
    combs = itertools.combinations(range(len(reps)), size)
    while True:
        chunk = list(itertools.islice(combs, 200000))
        if not chunk:
            break
        idx = np.array(chunk)
        Ms = Ar[:, idx].transpose(1, 0, 2)  # (B, r, size)
        x, *_ = zip(*[np.linalg.lstsq(Mx, br, rcond=None)[:1] for Mx in Ms]) if False else (None,)
        G = np.einsum('bri,brj->bij', Ms, Ms) + 1e-12 * np.eye(size)
        rhs = np.einsum('bri,r->bi', Ms, br)
        sol = np.linalg.solve(G, rhs[..., None])[..., 0]
        res = np.linalg.norm(np.einsum('bri,bi->br', Ms, sol) - br, axis=1)
        for b in np.nonzero(res < 1e-6 * np.linalg.norm(br))[0]:
            C = [reps[i] for i in idx[b]]
            Ae = Mu[:, C]
            if rank_modp(np.column_stack([Ae, Mmax])) == rank_modp(Ae):
                hits.append(C)
        if len(hits) >= 5:
            break
    print('size', size, 'exact hits', len(hits), flush=True)
    for C in hits[:5]:
        print('   ', [(keys[c][0], sorted(keys[c][1])) for c in C])
    if hits:
        break
