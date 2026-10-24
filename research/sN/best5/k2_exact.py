"""EXACT exhaustive search: can max_5 = R + d1 relu(g1) + d2 relu(g2) hold (free remainder R,
translation-invariant pair neurons g_k, d_k = +-1)?  Necessary conditions used (3-locality germs):
for every 3-locality L = (T, (o1,o2)) the third mixed difference of max_5 - R is delta, and that
of d relu(g) is  delta * d * X_g(T) * [g vanishes on C_L],
   g vanishes on C_L  <=>  v(T) = v(T+o1) = 0,         v(S) := g(1_S),
   X_g(T) = sum_{t in T} relu(v(t)) - sum_{P subset T, |P|=2} relu(v(P))
          = (sum_t |v(t)| - sum_P |v(P)|) / 2           (uses v(T) = 0 and the order-2 identity).
So  sum_k d_k [k covers L] X_k(T_L) = 1  for all 20 localities.            (E)
Search: every neuron lies in the generic part of a vanishing flat V_Z (Z = exact set of 3-/4-sets
where v = 0; flats_loc.pkl).  For every pair of flats whose coverage is complete (cover_pairs.pkl),
up to the S5 action, and every d in {+-1}^2, we enumerate the closed sign chambers of the
singleton/pair forms relevant to the covered T's and decide (E) exactly by Gaussian elimination +
Fourier-Motzkin over Fractions (closed chambers: a relaxation, so 'infeasible' is a proof).
Output: list of surviving (pair, d, chambers) or 'NO SURVIVOR'."""
import pickle, itertools, sys, time
from fractions import Fraction as Fr
from flats_loc import vrow, REL, N
import exact_lp
d0 = pickle.load(open('cover_pairs.pkl', 'rb'))
from flats_loc import nullspace as _ns, TRANS as _TR, RROWS as _RR


class _LazyFlats(dict):
    # flat Z (closure bitmask over REL) -> (dim, exact basis of V_Z), computed on demand (memory)
    def __missing__(self, Z):
        B = _ns([_TR] + [_RR[i] for i in range(len(_RR)) if Z >> i & 1])
        self[Z] = (len(B), B)
        return self[Z]

    def __contains__(self, Z):
        return True


F = _LazyFlats()
LOCS = d0['LOCS']; bymask = d0['bymask']; PAIRSM = d0['pairs']
IDX = {S: i for i, S in enumerate(REL)}
SMALL = [frozenset([i]) for i in range(N)] + [frozenset(p) for p in itertools.combinations(range(N), 2)]
PERMS = list(itertools.permutations(range(N)))
TARGET = [Fr(1)] * len(LOCS)   # third mixed difference of max_5 (units of delta) at each locality


def permZ(Z, p):
    out = 0
    for i, S in enumerate(REL):
        if Z >> i & 1:
            out |= 1 << IDX[frozenset(p[x] for x in S)]
    return out


def cov(Z):
    return [q for q, (T, o) in enumerate(LOCS) if Z >> IDX[T] & 1 and Z >> IDX[T | {o}] & 1]


# ---------- exact closed-system feasibility ----------
def fm_closed(ineq, n):
    """exists z in R^n with  c0 + c.z >= 0 for all rows (c0, c)?  rows are lists [c0, c1..cn]."""
    rows = [list(r) for r in ineq]
    for var in range(1, n + 1):
        pos = [r for r in rows if r[var] > 0]; neg = [r for r in rows if r[var] < 0]
        new = [r for r in rows if r[var] == 0]
        for p in pos:
            for q in neg:
                new.append([p[t] * (-q[var]) + q[t] * p[var] for t in range(n + 1)])
        seen = set(); rows = []
        for r in new:
            g = max((abs(c) for c in r[1:]), default=0)
            if g == 0:
                if r[0] < 0: return False
                continue
            k = tuple(c / g for c in r)
            if k not in seen:
                seen.add(k); rows.append(list(k))
        if len(rows) > 4000:
            raise RuntimeError('FM blowup')
    return all(r[0] >= 0 for r in rows)


def solve_eq(E, n):
    """E rows [c0, c1..cn] meaning c0 + c.x = 0.  Returns (x0, Nbasis) affine param or None."""
    M = [list(r[1:]) + [-r[0]] for r in E]; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; inv = 1 / M[r][c]; M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    if any(all(x == 0 for x in row[:n]) and row[n] != 0 for row in M[r:]):
        return None
    x0 = [Fr(0)] * n
    for row, pc in zip(M[:r], piv): x0[pc] = row[n]
    free = [c for c in range(n) if c not in piv]; NB = []
    for f in free:
        v = [Fr(0)] * n; v[f] = Fr(1)
        for row, pc in zip(M[:r], piv): v[pc] = -row[f]
        NB.append(v)
    return x0, NB


def feasible_fm(E, I, n):
    """E: equalities [c0,c..], I: inequalities [c0,c..] >= 0 over x in R^n."""
    s = solve_eq(E, n) if E else ([Fr(0)] * n, [[Fr(1) if i == j else Fr(0) for i in range(n)] for j in range(n)])
    if s is None: return False
    x0, NB = s; m = len(NB)
    rows = []
    for r in I:
        c0 = r[0] + sum(a * b for a, b in zip(r[1:], x0))
        cz = [sum(a * b for a, b in zip(r[1:], v)) for v in NB]
        rows.append([c0] + cz)
    if m == 0:
        return all(r[0] >= 0 for r in rows)
    return fm_closed(rows, m)


# ---------- per-flat data ----------
def forms(Z):
    dim, B = F[Z]
    return {S: [sum(a * b for a, b in zip(vrow(S), v)) for v in B] for S in SMALL}, dim


def strict_feasible(rows, n):
    # homogeneous strict system r.x > 0: reuse closed FM on r.x >= 1 (homogeneous scaling)
    return fm_closed([[Fr(-1)] + list(r) for r in rows], n)


def chambers(hyps, n):
    """closed full-dimensional sign chambers of nonzero forms hyps (list of (S, form))"""
    out = []
    def rec(i, cons, signs):
        if i == len(hyps):
            out.append(dict(signs)); return
        S, h = hyps[i]
        for s in (1, -1):
            c2 = cons + [[s * x for x in h]]
            if strict_feasible(c2, n):
                rec(i + 1, c2, signs + [(S, s)])
    rec(0, [], [])
    return out


def X_form(T, fm, signs):
    """X(T) on a chamber as a linear form (list) in the flat coordinates"""
    n = len(next(iter(fm.values())))
    v = [Fr(0)] * n
    for S in SMALL:
        if S <= T:
            sg = signs.get(S, 0)
            if sg == 0: continue  # identically zero form
            w = Fr(1, 2) * sg * (1 if len(S) == 1 else -1)
            v = [a + w * b for a, b in zip(v, fm[S])]
    return v


def neuron_data(Z):
    fm, n = forms(Z)
    Cv = cov(Z); Ts = sorted({LOCS[q][0] for q in Cv}, key=sorted)
    rel = [S for S in SMALL if any(S <= T for T in Ts) and any(fm[S])]
    # dedupe parallel forms keeps correctness simple: keep all (FM handles)
    chs = chambers([(S, fm[S]) for S in rel], n)
    data = []
    for sg in chs:
        X = {T: X_form(T, fm, sg) for T in Ts}
        ineq = [[Fr(0)] + [sg[S] * x for x in fm[S]] for S in rel]
        data.append((X, ineq))
    return n, Cv, data


def check_pair(Z1, Z2, cache, stats):
    """joint DFS over the triples T: branch on the closed signs of the singleton/pair forms of both
    neurons inside T (only for neurons covering a locality of T), then impose the locality
    equations of T; prune by exact feasibility (Gauss + Fourier-Motzkin over Fractions)."""
    res = []
    for Z in (Z1, Z2):
        if Z not in cache:
            fm, n = forms(Z); cache[Z] = (fm, n, set(cov(Z)))
    (fm1, n1, C1), (fm2, n2, C2) = cache[Z1], cache[Z2]
    n = n1 + n2
    FM = (fm1, fm2); CC = (C1, C2); OFF = (0, n1)
    def lift(k, form):
        return ([Fr(0)] + list(form) + [Fr(0)] * n2) if k == 0 else ([Fr(0)] + [Fr(0)] * n1 + list(form))
    Ts = sorted({LOCS[q][0] for q in C1 | C2}, key=sorted)
    coversT = {(k, T): any(LOCS[q][0] == T for q in CC[k]) for k in (0, 1) for T in Ts}
    for d in itertools.product((1, -1), repeat=2):
        def rec(ti, signs, E, I):
            stats[0] += 1
            if res and res[-1][0] == d:
                return  # one witness per sign pattern d suffices
            if ti == len(Ts):
                res.append((d, dict(signs))); return
            T = Ts[ti]
            todo = [(k, S) for k in (0, 1) if coversT[(k, T)] for S in SMALL
                    if S <= T and (k, S) not in signs and any(FM[k][S])]
            def branch(i, signs, I):
                if i == len(todo):
                    E2 = list(E)
                    for q, (TT, o) in enumerate(LOCS):
                        if TT != T: continue
                        row = [-TARGET[q]] + [Fr(0)] * n
                        for k in (0, 1):
                            if q in CC[k]:
                                for S in SMALL:
                                    sg = signs.get((k, S), 0)
                                    if S <= T and sg:
                                        w = Fr(1, 2) * d[k] * sg * (1 if len(S) == 1 else -1)
                                        for t, x in enumerate(FM[k][S]):
                                            row[1 + OFF[k] + t] += w * x
                        E2.append(row)
                    if exact_lp.feasible(E2, I, n):
                        rec(ti + 1, signs, E2, I)
                    return
                if res and res[-1][0] == d:
                    return
                k, S = todo[i]
                for sg in (1, -1):
                    r = lift(k, [sg * x for x in FM[k][S]])
                    if exact_lp.feasible(E, I + [r], n):
                        sg2 = dict(signs); sg2[(k, S)] = sg
                        branch(i + 1, sg2, I + [r])
            branch(0, signs, I)
        rec(0, {}, [], [])
    return res


if __name__ == '__main__':
    t0 = time.time()
    # canonical pairs under S5 (and swap)
    import os
    if os.path.exists('k2_work.pkl'):
        work = pickle.load(open('k2_work.pkl', 'rb'))
    else:
      seen = set(); work = []
      for a, b in PAIRSM:
        for Z1 in bymask[a]:
            for Z2 in bymask[b]:
                key = min(min((permZ(Z1, p), permZ(Z2, p)), (permZ(Z2, p), permZ(Z1, p))) for p in PERMS)
                if key not in seen:
                    seen.add(key); work.append(key)
      pickle.dump(work, open('k2_work.pkl', 'wb'))
    print('flat pairs up to S5 and swap:', len(work), '%.0fs' % (time.time() - t0), flush=True)
    cache = {}; stats = [0]; surv = []
    done = {}
    if os.path.exists('k2_done.txt'):
        for line in open('k2_done.txt'):
            i, ok = line.split()[:2]; done[int(i)] = ok
    out = open('k2_done.txt', 'a')
    for i, (Z1, Z2) in enumerate(work):
        if i in done:
            if done[i] != 'excluded': surv.append((Z1, Z2))
            continue
        r = check_pair(Z1, Z2, cache, stats)
        if r:
            surv.append((Z1, Z2))
            print('SURVIVOR', i, Z1, Z2, F[Z1][0], F[Z2][0], sorted({x[0] for x in r}), flush=True)
        out.write('%d %s %d %d %s\n' % (i, 'SURVIVOR' if r else 'excluded', Z1, Z2, sorted({x[0] for x in r}) if r else ''))
        out.flush()
        if len(cache) > 400: cache.clear()
        if i % 20 == 0:
            print('progress', i, len(work), 'nodes', stats[0], 'LP', exact_lp.STATS, 'survivors', len(surv), '%.0fs' % (time.time() - t0), flush=True)
    print('DONE pairs', len(work), 'nodes', stats[0], 'LP', exact_lp.STATS, 'survivors', len(surv), '%.0fs' % (time.time() - t0))
    pickle.dump(surv, open('k2_survivors.pkl', 'wb'))
