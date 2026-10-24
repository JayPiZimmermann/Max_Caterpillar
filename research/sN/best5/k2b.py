"""Two-phase EXACT version of the K-neuron locality search (same mathematics as k2_exact.py,
PROOFS.md §k-search).  For a tuple of flats and signs d, the locality equations (E) are reduced
per triple T to constraints on the numbers X_k(T); constraints involving one neuron are checked
first per neuron (cached), joint constraints afterwards.  Pruning only with exactly certified
infeasibility (exact_lp.feasible).  Usage: python k2b.py  (resumable via k2b_done.txt)"""
import sys, os, time, pickle, itertools
from fractions import Fraction as Fr
import exact_lp
from k2_exact import LOCS, cov, forms, SMALL, F, TARGET

TRIPLES = sorted({T for T, o in LOCS}, key=sorted)
LOC_OF_T = {T: [q for q, (TT, o) in enumerate(LOCS) if TT == T] for T in TRIPLES}


def reduce_constraints(covers, d):
    """covers: list over neurons of sets of covered localities.  Returns (ok, cons) where cons is a
    list of (T, {k: coef}, rhs) or ok=False if inconsistent at the level of the X-variables."""
    K = len(covers); cons = []
    for T in TRIPLES:
        eqs = []
        for q in LOC_OF_T[T]:
            ks = [k for k in range(K) if q in covers[k]]
            if not ks:
                if TARGET[q] == 0: continue
                return False, None
            eqs.append(({k: Fr(d[k]) for k in ks}, TARGET[q]))
        # exact elimination in the |K| unknowns X_k(T)
        if not eqs: continue
        rows = [[c.get(k, Fr(0)) for k in range(K)] + [r] for c, r in eqs]
        M = [list(r) for r in rows]; piv = []; rr = 0
        for c in range(K):
            p = next((i for i in range(rr, len(M)) if M[i][c] != 0), None)
            if p is None: continue
            M[rr], M[p] = M[p], M[rr]; inv = 1 / M[rr][c]; M[rr] = [x * inv for x in M[rr]]
            for i in range(len(M)):
                if i != rr and M[i][c] != 0:
                    f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[rr])]
            piv.append(c); rr += 1
        if any(all(x == 0 for x in row[:K]) and row[K] != 0 for row in M[rr:]):
            return False, None
        for row in M[:rr]:
            cons.append((T, {k: row[k] for k in range(K) if row[k] != 0}, row[K]))
    return True, cons


def dfs(Zs, cons, stats):
    """exists v_k in V_{Z_k} with sum_k coef_k X_k(T) = rhs for all constraints?  (certified pruning)"""
    data = [forms(Z) for Z in Zs]
    offs = [0]
    for fm, n in data: offs.append(offs[-1] + n)
    n = offs[-1]
    Ts = []
    for T, c, r in sorted(cons, key=lambda t: len(t[1])):
        if T not in Ts: Ts.append(T)
    found = [False]

    def lift(k, form):
        row = [Fr(0)] * (n + 1)
        for t, x in enumerate(form): row[1 + offs[k] + t] = x
        return row

    def rec(ti, signs, E, I):
        stats[0] += 1
        if found[0]: return
        if ti == len(Ts):
            found[0] = True; return
        T = Ts[ti]
        ks = sorted({k for TT, c, r in cons if TT == T for k in c})
        todo = [(k, S) for k in ks for S in SMALL if S <= T and (k, S) not in signs and any(data[k][0][S])]

        def branch(i, signs, I):
            if found[0]: return
            if i == len(todo):
                E2 = list(E)
                for TT, c, r in cons:
                    if TT != T: continue
                    row = [-r] + [Fr(0)] * n
                    for k, coef in c.items():
                        fm = data[k][0]
                        for S in SMALL:
                            sg = signs.get((k, S), 0)
                            if S <= T and sg:
                                w = coef * Fr(1, 2) * sg * (1 if len(S) == 1 else -1)
                                for t, x in enumerate(fm[S]):
                                    row[1 + offs[k] + t] += w * x
                    E2.append(row)
                if exact_lp.feasible(E2, I, n):
                    rec(ti + 1, signs, E2, I)
                return
            k, S = todo[i]
            for sg in (1, -1):
                r = lift(k, [sg * x for x in data[k][0][S]])
                if exact_lp.feasible(E, I + [r], n):
                    s2 = dict(signs); s2[(k, S)] = sg
                    branch(i + 1, s2, I + [r])
        branch(0, signs, I)
    rec(0, {}, [], [])
    return found[0]


SINGLE_CACHE = {}


def check(Zs, stats):
    covers = [set(cov(Z)) for Z in Zs]
    K = len(Zs); surv = []
    for d in itertools.product((1, -1), repeat=K):
        ok, cons = reduce_constraints(covers, d)
        if not ok:
            continue
        good = True
        for k in range(K):
            mine = [(T, {0: c[k]}, r) for T, c, r in cons if set(c) == {k}]
            key = (Zs[k], tuple(sorted((tuple(sorted(T)), c[0], r) for T, c, r in mine)))
            if key not in SINGLE_CACHE:
                SINGLE_CACHE[key] = dfs([Zs[k]], mine, stats)
            if not SINGLE_CACHE[key]:
                good = False; break
        if not good:
            continue
        joint = [c for c in cons if len(c[1]) > 1]
        if not joint or dfs(list(Zs), cons, stats):
            surv.append(d)
    return surv


if __name__ == '__main__':
    t0 = time.time()
    work = pickle.load(open('k2_work.pkl', 'rb'))
    done = set()
    if os.path.exists('k2b_done.txt'):
        done = {int(l.split()[0]) for l in open('k2b_done.txt')}
    out = open('k2b_done.txt', 'a'); stats = [0]; nsurv = 0
    for i, (Z1, Z2) in enumerate(work):
        if i in done: continue
        s = check([Z1, Z2], stats)
        out.write('%d %s %d %d %s\n' % (i, 'SURVIVOR' if s else 'excluded', Z1, Z2, s)); out.flush()
        if s:
            nsurv += 1; print('SURVIVOR', i, Z1, Z2, F[Z1][0], F[Z2][0], s, flush=True)
        if len(SINGLE_CACHE) > 20000: SINGLE_CACHE.clear()
        if i % 20 == 0:
            print('progress', i, len(work), 'nodes', stats[0], 'LP', exact_lp.STATS, 'new survivors', nsurv,
                  '%.0fs' % (time.time() - t0), flush=True)
    print('DONE', len(work), 'nodes', stats[0], 'LP', exact_lp.STATS, '%.0fs' % (time.time() - t0))
