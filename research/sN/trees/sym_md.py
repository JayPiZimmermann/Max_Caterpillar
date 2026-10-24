#!/usr/bin/env python3
"""Symmetry-reduced instrument (research/sN/trees).

Symmetric origin tests: for a multiset p of step values, T_p f = sum_{delta in orbit(p)} MD_delta f,
MD_delta f = sum_{S subset [m]} (-1)^{m-|S|} f(delta_S)  (box at the full tie, steps delta).
T_p is S_m-invariant, so it suffices to evaluate germ orbit representatives.  If max_m is not in
the span (over the tests) of a germ family, an explicit symmetric functional Lambda = sum_p c_p T_p
kills the family and not max_m; we solve for it (mod p, then rational reconstruction attempt).
Family 'two': germs G(0, v, F) with a vertex having >= 2 out-leaves (leaf l, term relu(z_l - z_c),
v_l = 0), F any oriented forest on {1..m-1}, heads |v_t| <= R, v_0 = -1, sum v = 0.
Usage: sym_md.py m R values(comma) [maxgerms]
"""
import sys, itertools, random
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from pn_test import forests, heads, rank_mod_p, P


def two_outleaves(v, F):
    deg = {}
    for i, j in F:
        deg[i] = deg.get(i, 0) + 1; deg[j] = deg.get(j, 0) + 1
    cnt = {}
    for (i, j) in F:
        if deg[i] == 1 and v[i] == 0:
            cnt[j] = cnt.get(j, 0) + 1
    return any(x >= 2 for x in cnt.values())


def twin_leaves(v, F):
    """two leaves of F at a common centre with the same orientation and the same head entry"""
    deg = {}
    for i, j in F:
        deg[i] = deg.get(i, 0) + 1; deg[j] = deg.get(j, 0) + 1
    sig = {}
    for (i, j) in F:
        if deg[i] == 1:
            key = (j, 'out', v[i]); sig[key] = sig.get(key, 0) + 1
        if deg[j] == 1:
            key = (i, 'in', v[j]); sig[key] = sig.get(key, 0) + 1
    return any(x >= 2 for x in sig.values())


MODE = {'pred': two_outleaves}


def canon(m, v, F):
    rest = list(range(1, m)); best = None
    for p in itertools.permutations(rest):
        mp = {0: 0}; mp.update(dict(zip(rest, p)))
        vv = [0] * m
        for t in range(m): vv[mp[t]] = v[t]
        FF = tuple(sorted((mp[i], mp[j]) for i, j in F))
        key = (tuple(vv), FF)
        if best is None or key < best: best = key
    return best


def family(m, R):
    rest = list(range(1, m)); seen = set(); out = []
    for F in forests(rest):
        for ori in itertools.product([0, 1], repeat=len(F)):
            FF = tuple((i, j) if o == 0 else (j, i) for (i, j), o in zip(F, ori))
            for v in heads(m, 0, R):
                if MODE['pred'](v, FF):
                    key = canon(m, v, FF)
                    if key not in seen:
                        seen.add(key); out.append(key)
    return out


def patterns(m, values):
    return list(itertools.combinations_with_replacement(values, m))


def orbit(p):
    return sorted(set(itertools.permutations(p)))


def eval_germ(v, F, Z):
    """Z: (n, m) integer array of points."""
    s = Z @ np.array(v, dtype=np.int64)
    for i, j in F:
        s = s + np.maximum(Z[:, i] - Z[:, j], 0)
    return np.maximum(s, 0)


def main():
    m, R = int(sys.argv[1]), int(sys.argv[2])
    values = [int(x) for x in sys.argv[3].split(',')]
    maxg = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9
    if len(sys.argv) > 5 and sys.argv[5] == 'twin':
        MODE['pred'] = twin_leaves
    fam = family(m, R)
    random.seed(1)
    if len(fam) > maxg:
        fam = random.sample(fam, maxg)
    pats = patterns(m, values)
    cube = np.array(list(itertools.product([0, 1], repeat=m)), dtype=np.int64)
    sign = np.array([(-1) ** (m - int(s.sum())) for s in cube], dtype=np.int64)
    # all (pattern, delta) points stacked
    blocks = []
    for p in pats:
        D = np.array(orbit(p), dtype=np.int64)            # (o, m)
        blocks.append(D)
    allD = np.concatenate(blocks)                         # (n_delta, m)
    sizes = [len(b) for b in blocks]
    Z = (allD[:, None, :] * cube[None, :, :]).reshape(-1, m)   # (n_delta*2^m, m)
    def features(fn):
        vals = fn(Z).reshape(len(allD), len(cube)) @ sign      # MD per delta
        out = []; pos = 0
        for sz in sizes:
            out.append(vals[pos:pos + sz].sum()); pos += sz
        return out
    rows = [features(lambda Z, v=v, F=F: eval_germ(v, F, Z)) for v, F in fam]
    mx = features(lambda Z: Z.max(axis=1))
    A = np.array(rows, dtype=np.int64).T                  # patterns x germs
    b = np.array(mx, dtype=np.int64)[:, None]
    r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, b], axis=1))
    print(f'm={m} R={R} values={values}: {len(fam)} germ reps, {len(pats)} symmetric tests; '
          f'rank {r1}, with max {r2} -> {"SEPARATED" if r2 > r1 else "not separated"}', flush=True)


if __name__ == '__main__':
    main()
