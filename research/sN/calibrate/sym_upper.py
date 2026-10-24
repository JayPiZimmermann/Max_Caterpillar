"""Upper bounds from subgroup-invariant expansions.

If (K, d) is an expansion of max_N and H <= S_N, then averaging over H gives
an H-invariant expansion supported on the union of the H-orbits meeting K.
Conversely, for a set of H-orbits O whose orbit-sum columns span b, the union
of O is a feasible support.  We find the cheapest such set of orbits (weight
= orbit size) by a weighted implicit hitting set (mod-P cuts, HiGHS), then
prune individual units greedily (mod P) and certify exactly on all cells.

usage: python sym_upper.py N group [seed]
groups: S_N, fix1 (S_{N-1}), S3xS2..., cyc (C_N), dih (D_N), A_N, trivial
"""
import sys, time, pickle, itertools
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix
from core import P, unit_perm_table
from fastmodp import rref
from sparse_space import SparseSpace
from modp import Space


def sign(p):
    s, seen = 1, set()
    for i in range(len(p)):
        if i in seen:
            continue
        j, L = i, 0
        while j not in seen:
            seen.add(j); j = p[j]; L += 1
        s *= (-1) ** (L - 1)
    return s


def group(N, name):
    allp = list(itertools.permutations(range(N)))
    if name == 'S_N':
        return allp
    if name == 'A_N':
        return [p for p in allp if sign(p) == 1]
    if name == 'fix1':
        return [p for p in allp if p[N - 1] == N - 1]
    if name == 'cyc':
        return [tuple((i + s) % N for i in range(N)) for s in range(N)]
    if name == 'dih':
        c = [tuple((i + s) % N for i in range(N)) for s in range(N)]
        return c + [tuple((s - i) % N for i in range(N)) for s in range(N)]
    if name.startswith('blocks'):          # e.g. blocks3-2 : S_3 x S_2
        sizes = [int(x) for x in name[6:].split('-')]
        cuts = np.cumsum([0] + sizes)
        return [p for p in allp if all(cuts[b] <= p[i] < cuts[b + 1]
                                       for b in range(len(sizes)) for i in range(cuts[b], cuts[b + 1]))]
    if name == 'trivial':
        return [tuple(range(N))]
    raise ValueError(name)


def weighted_ihs(cols, w, b, rng, tl=300, max_it=500, log=print):
    """cols: (rows x m) int64 mod P; w: weights; b: target.  Returns chosen idx."""
    m = cols.shape[1]
    cuts = []
    for it in range(max_it):
        if cuts:
            rows = np.repeat(np.arange(len(cuts)), [len(c) for c in cuts])
            cc = np.concatenate([np.array(sorted(c)) for c in cuts])
            A = csr_matrix((np.ones(len(cc)), (rows, cc)), shape=(len(cuts), m))
            res = milp(np.array(w, float), constraints=LinearConstraint(A, lb=1, ub=np.inf),
                       integrality=np.ones(m), bounds=Bounds(0, 1), options={'time_limit': tl})
            K = [int(i) for i in np.flatnonzero(res.x > 0.5)]
            lb = getattr(res, 'mip_dual_bound', None)
        else:
            K, lb, res = [], 0, None
        sub = cols[:, K] if K else np.zeros((cols.shape[0], 0), dtype=np.int64)
        _, p1 = rref(sub) if K else (None, [])
        _, p2 = rref(np.hstack([sub, b[:, None]]))
        feas = len(p1) == len(p2)
        log(f'  ihs it {it}: cuts {len(cuts)} weight {sum(w[k] for k in K)} dual {lb} feasible {feas}')
        if feas:
            return K
        Ks = set(K)
        for rep in range(2):
            order = K + [int(u) for u in rng.permutation(m) if u not in Ks]
            M = np.hstack([b[:, None], cols[:, order]])
            R, piv = rref(M)
            cut = frozenset(order[i] for i in np.flatnonzero(R[0, 1:]))
            assert not (cut & Ks)
            cuts.append(cut)
    return None


def main():
    N, gname = int(sys.argv[1]), sys.argv[2]
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = np.random.default_rng(seed)
    ss = SparseSpace(N)
    sp = Space(N)
    H = group(N, gname)
    perms, T = unit_perm_table(N, sp.U)
    pidx = {p: i for i, p in enumerate(perms)}
    TH = T[[pidx[p] for p in H]]
    orbits, seen = [], set()
    for u in range(ss.n):
        if u not in seen:
            o = sorted(set(int(x) for x in TH[:, u]))
            seen |= set(o)
            orbits.append(o)
    cols = np.stack([ss.A[:, o].sum(axis=1) for o in orbits], axis=1) % P
    nz = np.flatnonzero(np.any(cols != 0, axis=1) | (ss.b != 0))
    cols, b = cols[nz], ss.b[nz] % P
    w = [len(o) for o in orbits]
    print(f'N={N} H={gname} |H|={len(H)} orbits {len(orbits)} rows {len(nz)}', flush=True)
    t0 = time.time()
    K = weighted_ihs(cols, w, b, rng, log=lambda s: print(s, flush=True))
    if K is None:
        print('no result'); return
    units = sorted(u for k in K for u in orbits[k])
    print(f'optimal H-invariant support (mod P): {len(units)} units in {len(K)} orbits, t={time.time()-t0:.0f}s', flush=True)
    pr = ss.prune(units, order=list(rng.permutation(units)))
    print('greedy-pruned support', len(pr), flush=True)
    res = sp.exact(pr)
    print('certified exactly on all cells:', res is not None, 'size', len(res[0]) if res else None, flush=True)
    if res:
        pickle.dump((gname, pr, res), open(f'data/sym_{N}_{gname}_{seed}.pkl', 'wb'))


if __name__ == '__main__':
    main()
