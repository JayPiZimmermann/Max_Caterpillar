"""Exact kink/Moebius formulation of caterpillar expansions (h5-growth branch).

Facts used (see README in this directory for the proof):
  f := sum_k d_k U_k - max_N lies in the auxiliary span A_N (up to the
  translation-equivariant reduction of the compilation proof) iff
   (KINK) inside every open braid cell the kinks of the units cancel, and
   (MOB)  for every S subset [N], |S| >= 3:
          sum_k d_k D_S U_k = D_S max_N = (-1)^{|S|+1},
          D_S g := sum_{R subset S} (-1)^{|S|-|R|} g(1_R).
Units: normalized descriptions (h, M) from scripts/vocabulary_search.dictionary,
non-auxiliary ones.  Everything here is integer arithmetic.
"""
import itertools
import os
import pickle
import sys
from math import gcd

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'scripts'))
import vocabulary_search as vs  # noqa: E402

DATA = os.path.join(HERE, 'data')
os.makedirs(DATA, exist_ok=True)


def units_of(N):
    f = os.path.join(DATA, f'units_{N}.pkl')
    if os.path.exists(f):
        return pickle.load(open(f, 'rb'))
    K0, _ = vs.dictionary(N)
    U = sorted(k for k in K0 if not vs.is_auxiliary(k))
    pickle.dump(U, open(f, 'wb'))
    return U


def subsets3(N):
    return [S for r in range(3, N + 1) for S in itertools.combinations(range(N), r)]


def unit_value_on_set(key, R):
    h, M = key
    a = sum(h[i] for i in R) + sum(1 for i, j in M if i in R and j not in R)
    return a if a > 0 else 0


def mobius_row(key, N):
    out = []
    for S in subsets3(N):
        tot = 0
        for r in range(len(S) + 1):
            for R in itertools.combinations(S, r):
                tot += (-1) ** (len(S) - r) * unit_value_on_set(key, set(R))
        out.append(tot)
    return out


def primitive(a):
    g = 0
    for t in a:
        g = gcd(g, abs(t))
    d = tuple(t // g for t in a)
    for t in d:
        if t:
            return (d, g) if t > 0 else (tuple(-s for s in d), -g)
    return None


def unit_kinks(N, key, perms):
    """[(perm_index, d, lam)] : on cell x_{pi0} > x_{pi1} > ..., U = relu(lam d.x)+lin,
    with a kink (prefix sums of the gradient change sign)."""
    h, M = key
    out = []
    for p, pi in enumerate(perms):
        pos = {v: t for t, v in enumerate(pi)}
        a = list(h)
        for i, j in M:
            if pos[i] < pos[j]:      # i above j: hinge active
                a[i] += 1
                a[j] -= 1
        s = 0
        pos_seen = neg_seen = False
        for t in range(N - 1):
            s += a[pi[t]]
            if s > 0:
                pos_seen = True
            elif s < 0:
                neg_seen = True
        if pos_seen and neg_seen:
            d, lam = primitive(a)
            out.append((p, d, abs(lam)))
    return out


def build(N):
    """Return U, kink groups {(p,d): {u: lam}}, Mobius matrix Dm (nS x nU), target tD."""
    f = os.path.join(DATA, f'system_{N}.pkl')
    if os.path.exists(f):
        return pickle.load(open(f, 'rb'))
    U = units_of(N)
    perms = list(itertools.permutations(range(N)))
    groups = {}
    for u, key in enumerate(U):
        for p, d, lam in unit_kinks(N, key, perms):
            groups.setdefault((p, d), {})[u] = lam
    Ss = subsets3(N)
    Dm = np.array([mobius_row(k, N) for k in U], dtype=np.int64).T
    tD = np.array([(-1) ** (len(S) + 1) for S in Ss], dtype=np.int64)
    res = (U, groups, Dm, tD)
    pickle.dump(res, open(f, 'wb'))
    return res


if __name__ == '__main__':
    N = int(sys.argv[1])
    U, groups, Dm, tD = build(N)
    kinkfree = [u for u in range(len(U)) if all(u not in g for g in groups.values())]
    print('N', N, 'units', len(U), 'kink groups', len(groups), 'kink-free units', len(kinkfree))
    sizes = {}
    for g in groups.values():
        sizes[len(g)] = sizes.get(len(g), 0) + 1
    print('group size histogram', sorted(sizes.items()))
