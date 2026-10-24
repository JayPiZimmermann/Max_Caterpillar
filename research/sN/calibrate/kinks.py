"""Kink structure of units on braid cells (exact, integer).

On the open braid cell C_pi = {x_pi(1) < ... < x_pi(N)}, A_k is linear with
gradient a = h + sum_{(i,j) in M, i above j in pi} (e_i - e_j); a.1 = 0.  U_k
has an interior kink along a.x = 0 iff a takes both signs on the cone rays
1_{pi(j..N)}, j = 2..N; the kink coefficient (in the basis relu(d.x), d
primitive, first nonzero entry positive) is |lambda| where a = lambda d.
max_N and all auxiliary functions are linear on the fine cells, so a relation
max_N = sum d_k U_k + R forces, for every (pi, d):
        sum_{k: kink of U_k on C_pi is d} |lambda_k| d_k = 0.        (KINK)
"""
import itertools
from math import gcd


def primitive(a):
    g = 0
    for t in a:
        g = gcd(g, abs(t))
    d = tuple(t // g for t in a)
    for t in d:
        if t:
            return (d, g) if t > 0 else (tuple(-s for s in d), -g)


def unit_kinks(N, key, perms=None):
    """List of (pi, d, |lambda|) for every braid cell crossed by the kink."""
    h, M = key
    out = []
    for pi in (perms or itertools.permutations(range(N))):
        pos = {v: r for r, v in enumerate(pi)}
        a = list(h)
        for i, j in M:
            if pos[i] > pos[j]:
                a[i] += 1
                a[j] -= 1
        s, pos_, neg_ = 0, False, False
        for r in range(N - 1, 0, -1):
            s += a[pi[r]]
            if s > 0:
                pos_ = True
            elif s < 0:
                neg_ = True
        if pos_ and neg_:
            d, lam = primitive(a)
            out.append((pi, d, abs(lam)))
    return out


def kink_groups(N, units):
    perms = list(itertools.permutations(range(N)))
    groups = {}
    per_unit = []
    for u, key in enumerate(units):
        ks = unit_kinks(N, key, perms)
        per_unit.append([(pi, d) for pi, d, _ in ks])
        for pi, d, lam in ks:
            groups.setdefault((pi, d), {})[u] = lam
    return groups, per_unit


if __name__ == '__main__':
    import sys, collections
    from core import units_of
    N = int(sys.argv[1])
    U = units_of(N)
    groups, per_unit = kink_groups(N, U)
    print('units', len(U), 'kink groups', len(groups))
    print('group size histogram', sorted(collections.Counter(len(g) for g in groups.values()).items()))
    print('kinks per unit histogram', sorted(collections.Counter(len(p) for p in per_unit).items()))
    # iterative pruning: a unit with a group in which it is alone (among live units) must have d_k = 0
    live = set(range(len(U)))
    changed = True
    while changed:
        changed = False
        for g in groups.values():
            l = [u for u in g if u in live]
            if len(l) == 1:
                live.discard(l[0]); changed = True
    print('live units after singleton pruning', len(live))
