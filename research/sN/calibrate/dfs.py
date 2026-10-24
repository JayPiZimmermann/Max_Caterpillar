"""Exhaustive search for small supports via kink closure (exact).

Problem (sparse_form.py): find K with  b in span of the columns A[:, K],
A = [KINK; D_S rows], b = (0, D_S max_N).  The rows are valid linear
functionals on the span of units, auxiliary functions and max_N, so
"no K of size <= m satisfies this" is a certified lower bound s_N >= m + 1.

Branching (complete for inclusion-minimal feasible K*):
  * root: K* contains a unit with D_[N] != 0 (the row of S = [N] must be hit);
    by S_N symmetry, the first unit is an orbit representative r_i of such
    units and the orbits of r_1..r_{i-1} are excluded.
  * if some kink group g meets K in exactly one unit, every minimal feasible
    K* containing K meets g \\ K (otherwise that unit's coefficient is 0 in
    the unique-up-to-the-rest solution: the kink row of g reads lam*d_u = 0,
    so d_u = 0 and K* \\ {u} is feasible, contradicting minimality); branch on
    the members of g \\ K with an exclusion chain.
  * if K is kink-closed: test feasibility; otherwise branch on every
    non-excluded unit (exclusion chain); in mode 'relaxed' only on units
    sharing a kink group with K (a minimal K* of the relaxed problem is
    connected in the kink-group hypergraph).
Mode 'relaxed' keeps only the D_[N] row (the problem s'_N <= s_N).
Feasibility: rank mod P; when the mod-P test says "infeasible" with A_K of
full column rank mod P the answer is exact (rank_Q(A_K|b) >= rank_P = |K|+1);
otherwise a Fraction elimination decides.
usage: python dfs.py N m [relaxed|full] [max_nodes]
"""
import sys, time, pickle, itertools
from fractions import Fraction
import numpy as np
from core import P, units_of, unit_perm_table
from fastmodp import rref


def exact_feasible(cols, b):
    """Exact test b in span(cols) over Q; cols list of dict row->int, b dict."""
    rows = sorted(set().union(*[set(c) for c in cols]) | set(b))
    M = [[Fraction(c.get(r, 0)) for c in cols] + [Fraction(b.get(r, 0))] for r in rows]
    n = len(cols)
    rnk, piv_cols = 0, []
    for c in range(n + 1):
        p = next((i for i in range(rnk, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        if c == n:
            return False
        M[rnk], M[p] = M[p], M[rnk]
        inv = 1 / M[rnk][c]
        M[rnk] = [v * inv for v in M[rnk]]
        for i in range(len(M)):
            if i != rnk and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * bb for a, bb in zip(M[i], M[rnk])]
        rnk += 1
    return True


def main():
    N, m = int(sys.argv[1]), int(sys.argv[2])
    mode = sys.argv[3] if len(sys.argv) > 3 else 'full'
    max_nodes = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 12
    U = units_of(N)
    d = np.load(f'data/sparse_{N}.npz')
    Kink, Dm, tD = d['Kink'], d['Dm'], d['tD']
    if mode == 'relaxed':
        Dm, tD = Dm[-1:], tD[-1:]          # S = [N] is the last subset
    nG, n = Kink.shape
    A = np.vstack([Kink, Dm])
    bvec = np.concatenate([np.zeros(nG, dtype=np.int64), tD])
    col = [{int(r): int(A[r, u]) for r in np.flatnonzero(A[:, u])} for u in range(n)]
    bd = {int(r): int(bvec[r]) for r in np.flatnonzero(bvec)}
    ugroups = [[int(r) for r in np.flatnonzero(Kink[:, u])] for u in range(n)]
    gmembers = [[int(u) for u in np.flatnonzero(Kink[g])] for g in range(nG)]
    perms, T = unit_perm_table(N, U)
    top = A.shape[0] - 1                  # D_[N] row
    active = [u for u in range(n) if A[top, u] != 0]
    reps, seen = [], set()
    for u in active:
        if u not in seen:
            orb = set(int(x) for x in T[:, u])
            seen |= orb
            reps.append((u, orb))
    print(f'N={N} m={m} mode={mode}: units {n}, groups {nG}, D-active {len(active)}, orbit reps {len(reps)}', flush=True)

    cnt = [0] * nG
    stats = {'nodes': 0, 'closed': 0, 'sol': None}
    t0 = time.time()

    def feasible(K):
        cols = [col[u] for u in K]
        rows = sorted(set().union(*[set(c) for c in cols]) | set(bd))
        Am = np.array([[c.get(r, 0) for c in cols] for r in rows], dtype=np.int64)
        bm = np.array([bd.get(r, 0) for r in rows], dtype=np.int64)
        _, p1 = rref(Am)
        _, p2 = rref(np.hstack([Am, bm[:, None]]))
        if len(p2) > len(p1) and len(p1) == len(K):
            return False                      # exact: rank_Q(A|b) >= |K|+1
        return exact_feasible(cols, bd)

    def add(u, K):
        K.append(u)
        for g in ugroups[u]:
            cnt[g] += 1

    def remove(u, K):
        K.pop()
        for g in ugroups[u]:
            cnt[g] -= 1

    def rec(K, X):
        stats['nodes'] += 1
        if stats['nodes'] > max_nodes:
            raise TimeoutError
        if stats['nodes'] % 200000 == 0:
            print(f'  nodes {stats["nodes"]} closed {stats["closed"]} t={time.time()-t0:.0f}s', flush=True)
        # find the most constrained unsatisfied group
        best, bestc = None, None
        for u in K:
            for g in ugroups[u]:
                if cnt[g] == 1:
                    c = [v for v in gmembers[g] if v not in X and cnt_in(v, K)]
                    if best is None or len(c) < len(bestc):
                        best, bestc = g, c
                        if not c:
                            return False
        if best is not None and len(K) < m:
            # lookahead: every unsatisfied group needs a new member; one new
            # unit can serve at most `mx` of them
            unsat = [g for u in K for g in ugroups[u] if cnt[g] == 1]
            unsat = set(unsat)
            cover = {}
            for g in unsat:
                for v in gmembers[g]:
                    if v not in X and v not in Kset:
                        cover[v] = cover.get(v, 0) + 1
            mx = max(cover.values()) if cover else 0
            if mx == 0 or len(K) + -(-len(unsat) // mx) > m:
                return False
        if best is None:
            stats['closed'] += 1
            if feasible(K):
                stats['sol'] = list(K)
                return True
            if len(K) >= m:
                return False
            if mode == 'relaxed':
                # a minimal feasible K* of the relaxed problem is connected in
                # the kink-group hypergraph (otherwise one part alone carries
                # D_[N] != 0), so K* \ K meets a group that meets K
                nb = set()
                for u in K:
                    for g in ugroups[u]:
                        nb.update(gmembers[g])
                cands = sorted(v for v in nb if v not in X and v not in Kset)
            else:
                cands = [v for v in range(n) if v not in X and v not in Kset]
        else:
            if len(K) >= m:
                return False
            cands = bestc
        X2 = set(X)
        for v in cands:
            add(v, K); Kset.add(v)
            if rec(K, X2):
                return True
            remove(v, K); Kset.discard(v)
            X2.add(v)
        return False

    Kset = set()

    def cnt_in(v, K):
        return v not in Kset

    excluded = set()
    for i, (r, orb) in enumerate(reps):
        K = []
        add(r, K); Kset.add(r)
        ok = rec(K, set(excluded))
        remove(r, K); Kset.discard(r)
        print(f' rep {i} (unit {r}): {"FOUND" if ok else "none"}; nodes {stats["nodes"]} closed {stats["closed"]} t={time.time()-t0:.0f}s', flush=True)
        if ok:
            print('SOLUTION', stats['sol'], [U[u] for u in stats['sol']], flush=True)
            pickle.dump(stats['sol'], open(f'data/dfs_sol_{N}_{mode}_{m}.pkl', 'wb'))
            return
        excluded |= orb
    print(f'EXHAUSTED: no feasible K with |K| <= {m} (mode {mode}); nodes {stats["nodes"]}', flush=True)


if __name__ == '__main__':
    main()
