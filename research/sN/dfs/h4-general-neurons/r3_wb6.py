"""Round 3.  Orbit sizes of the Wang-Basu (arXiv:2608.25221v1, Thm 3.1, as relayed by a
web summary -- coefficients NOT trusted) N=6 seven-orbit identity, and an exact
re-solve: is max_6 in span(pair span + all labelled atoms of these 7 patterns)?
Counts the labelled atoms that are genuine neurons (not in the pair span).
Usage: python r3_wb6.py
"""
import itertools
import numpy as np

N = 6
PATS = {'P0': ('11', '11', '11', '11'), 'P22': ('11', '12', '11', '34'), 'P51': ('11', '12', '34', '56'),
        'P71': ('11', '22', '34', '56'), 'P130': ('12', '13', '14', '56'), 'P135': ('12', '13', '24', '56'),
        'P136': ('12', '13', '45', '46')}


def atoms_of(pat):
    letters = sorted(set(''.join(pat)))
    out = set()
    for img in itertools.permutations(range(N), len(letters)):
        f = dict(zip(letters, img))
        m = [tuple(sorted((f[s[0]], f[s[1]]))) for s in pat]
        L = tuple(sorted(m[:2])); R = tuple(sorted(m[2:]))
        out.add(tuple(sorted([L, R])))
    return sorted(out)


rng = np.random.default_rng(0)
X = rng.standard_normal((4000, N))
mv = lambda s: np.maximum(X[:, s[0]], X[:, s[1]])
cols, tot = [], 0
for name, pat in PATS.items():
    A = atoms_of(pat)
    genuine = 0
    for L, R in A:
        a = mv(L[0]) + mv(L[1]); b = mv(R[0]) + mv(R[1])
        d = a - b
        if d.min() < -1e-12 and d.max() > 1e-12:
            genuine += 1
            cols.append(np.maximum(a, b))
    tot += genuine
    print(name, pat, 'labelled atoms', len(A), 'genuine neurons', genuine)
print('total genuine neurons', tot)
F = np.concatenate([X] + [np.maximum(X[:, i] - X[:, j], 0)[:, None] for i, j in itertools.combinations(range(N), 2)], 1)
B = np.concatenate([np.array(cols).T, F], 1)
y = X.max(1)
c, *_ = np.linalg.lstsq(B, y, rcond=None)
print('max_6 in span: rel residual %.2e' % (np.linalg.norm(B @ c - y) / np.linalg.norm(y)))
