"""EXACT second stage for survivors of k2b.py: add the 4-tie and 5-tie germ equations.
For U in {3-sets, 4-sets, [5]} put Q_U(v) = 1/2 sum_{0 != W proper subset of U} (-1)^(|U|-|W|) |v(W)|
(= mu_U(relu v) when v(U) = 0).  Equations (PROOFS.md §k-search):
  3-localities (T,o):  sum_{k: v_k(T)=v_k(T+o)=0} d_k Q_T(v_k) = 1
  4-ties J:            sum_{k: v_k(J)=0}           d_k Q_J(v_k) = -1
  5-tie:               sum_k                       d_k Q_[5](v_k) = 1
Neurons range over their whole flat V_Z (relaxation); closed sign branches; certified pruning.
Usage: python k2c.py done_file  -> re-examines every SURVIVOR line."""
import sys, itertools, time
from fractions import Fraction as Fr
import exact_lp
from k2_exact import LOCS, cov, forms, F, REL, IDX, N
from k2b import reduce_constraints

ALLSETS = [frozenset(c) for r in range(1, N) for c in itertools.combinations(range(N), r)]
FOUR = [S for S in REL if len(S) == 4]
FULL = frozenset(range(N))


def allforms(Z):
    dim, B = F[Z]
    from flats_loc import vrow
    return {S: [sum(a * b for a, b in zip(vrow(S), v)) for v in B] for S in ALLSETS}, dim


def full_check(Zs, d, stats, use5=True):
    K = len(Zs)
    covers = [set(cov(Z)) for Z in Zs]
    ok, cons3 = reduce_constraints(covers, d)
    if not ok: return False
    cons = [(U, c, r) for U, c, r in cons3]
    for J in FOUR:
        ks = [k for k in range(K) if Zs[k] >> IDX[J] & 1]
        if not ks: return False
        cons.append((J, {k: Fr(d[k]) for k in ks}, Fr(-1)))
    if use5:
        cons.append((FULL, {k: Fr(d[k]) for k in range(K)}, Fr(1)))
    data = [allforms(Z) for Z in Zs]
    offs = [0]
    for fm, n in data: offs.append(offs[-1] + n)
    n = offs[-1]
    order = sorted(range(len(cons)), key=lambda i: (len(cons[i][0]), len(cons[i][1])))
    found = [False]

    def lift(k, form):
        row = [Fr(0)] * (n + 1)
        for t, x in enumerate(form): row[1 + offs[k] + t] = x
        return row

    def rec(oi, signs, E, I):
        stats[0] += 1
        if found[0]: return
        if oi == len(order):
            found[0] = True; return
        U, c, r = cons[order[oi]]
        todo = [(k, W) for k in sorted(c) for W in ALLSETS if W < U and (k, W) not in signs and any(data[k][0][W])]

        def branch(i, signs, I):
            if found[0]: return
            if i == len(todo):
                row = [-r] + [Fr(0)] * n
                for k, coef in c.items():
                    for W in ALLSETS:
                        sg = signs.get((k, W), 0)
                        if W < U and sg:
                            w = coef * Fr(1, 2) * sg * (-1) ** (len(U) - len(W))
                            for t, x in enumerate(data[k][0][W]):
                                row[1 + offs[k] + t] += w * x
                E2 = E + [row]
                if exact_lp.feasible(E2, I, n):
                    rec(oi + 1, signs, E2, I)
                return
            k, W = todo[i]
            for sg in (1, -1):
                rr = lift(k, [sg * x for x in data[k][0][W]])
                if exact_lp.feasible(E, I + [rr], n):
                    s2 = dict(signs); s2[(k, W)] = sg
                    branch(i + 1, s2, I + [rr])
        branch(0, signs, I)
    rec(0, {}, [], [])
    return found[0]


if __name__ == '__main__':
    t0 = time.time(); stats = [0]
    for line in open(sys.argv[1]):
        p = line.split()
        if p[1] != 'SURVIVOR': continue
        Zs = [int(p[2]), int(p[3])]
        res4 = [dd for dd in itertools.product((1, -1), repeat=2) if full_check(Zs, dd, stats, use5=False)]
        res5 = [dd for dd in res4 if full_check(Zs, dd, stats, use5=True)]
        print(p[0], 'dims', F[Zs[0]][0], F[Zs[1]][0], 'with 4-ties:', res4, 'with 4- and 5-tie:', res5,
              'nodes', stats[0], 'LP', exact_lp.STATS, '%.0fs' % (time.time() - t0), flush=True)
