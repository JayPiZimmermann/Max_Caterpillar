#!/usr/bin/env python3
"""Fast exact W_m(N) for the mixed-difference m-locality test (global/mixed_fast.py).

Same quantity as mixed_m.py (which brute-force checks the DP against direct
evaluation for N <= 6), with exact pruning:
  * every o with kappa_o < 0 or kappa_o > deg_F(o) must lie in T
    (outside, o needs exactly kappa_o hinge neighbours above it);
  * every t in T needs v_t != 0 or a hinge neighbour in T, otherwise the
    restricted function does not depend on z_t and D_L vanishes; if
    deg_F(t) = 0 then v_t = kappa_t, so such t needs kappa_t != 0.
Usage: python3 mixed_fast.py N m [workers]
"""
import itertools
import math
import sys
from fractions import Fraction
from multiprocessing import Pool

N = int(sys.argv[1])
m = int(sys.argv[2])
WORK = int(sys.argv[3]) if len(sys.argv) > 3 else 4
r = N - 2


def relu(t):
    return t if t > 0 else 0


def caterpillar(S):
    edges = []
    for j in range(1, r + 1):
        p = max([0] + [i for i in S if i < j])
        edges.append((p + 1, j + 1))
    return edges, max(S) + 1


SUBSETS = {}


def mixed(T, v, inner):
    tot = 0
    k = len(T)
    for mask in range(1 << k):
        Ss = {T[i] for i in range(k) if mask >> i & 1}
        a = sum(v[t] for t in Ss) + sum(relu((p in Ss) - (c in Ss)) for p, c in inner)
        if a > 0:
            tot += a if (k - len(Ss)) % 2 == 0 else -a
    return tot


def unit_weight(edges, last, states):
    kappa = [0] * N
    kappa[0] -= 1
    kappa[last] += 1
    nbr = [[] for _ in range(N)]
    lin, hin = [], []
    for (p, c), s in zip(edges, states):
        if s == 1:
            lin.append((p, c)); kappa[p] += 1; kappa[c] -= 1
        elif s == 2:
            hin.append((p, c)); kappa[p] += 1
            nbr[p].append(c); nbr[c].append(p)
    forced = [o for o in range(N) if kappa[o] < 0 or kappa[o] > len(nbr[o])]
    if len(forced) > m:
        return Fraction(0), None
    cand = [o for o in range(N) if o not in forced and (kappa[o] != 0 or nbr[o])]
    need = m - len(forced)
    if need > len(cand):
        return Fraction(0), None
    W = Fraction(0)
    best_T = []
    fo = math.factorial(N - m)
    for extra in itertools.combinations(cand, need):
        T = tuple(sorted(forced + list(extra)))
        Ts = set(T)
        rest = [o for o in range(N) if o not in Ts]
        ok = True
        for o in rest:
            inT = sum(1 for u in nbr[o] if u in Ts)
            if kappa[o] - inT < 0 or kappa[o] - inT > len(nbr[o]) - inT:
                ok = False
                break
        if not ok:
            continue
        if any(not (kappa[t] != 0 or nbr[t]) for t in T):
            continue
        v = {t: 0 for t in T}
        if last in Ts: v[last] += 1
        if 0 in Ts: v[0] -= 1
        for p, c in lin:
            if p in Ts: v[p] += 1
            if c in Ts: v[c] -= 1
        inner = []
        for p, c in hin:
            if p in Ts and c in Ts:
                inner.append((p, c))
            elif p in Ts:
                v[p] += 1
        if mixed(list(T), v, inner) == 0:
            continue
        idx = {o: k for k, o in enumerate(rest)}
        count = {0: 1}
        for _ in range(len(rest)):
            new = {}
            for placed, c in count.items():
                for o in rest:
                    b = 1 << idx[o]
                    if placed & b:
                        continue
                    above = sum(1 for u in nbr[o] if u in Ts or placed & (1 << idx[u]))
                    if above == kappa[o]:
                        new[placed | b] = new.get(placed | b, 0) + c
            count = new
        cnt = sum(count.values())
        if cnt:
            W += Fraction(cnt, fo)
            best_T.append((T, Fraction(cnt, fo)))
    return W, (kappa, hin, lin, best_T)


def job(S):
    edges, last = caterpillar(S)
    best, cfg = Fraction(0), None
    hist = {}
    for states in itertools.product(range(3), repeat=r):
        W, info = unit_weight(edges, last, states)
        hist[W] = hist.get(W, 0) + 1
        if W > best:
            best, cfg = W, (S, states, info)
    return best, cfg, hist


if __name__ == '__main__':
    Ss = [S for size in range(1, r + 1) for S in itertools.combinations(range(1, r + 1), size)]
    with Pool(WORK) as pool:
        res = pool.map(job, Ss, chunksize=1)
    best, cfg = max(((b, c) for b, c, _ in res), key=lambda t: t[0])
    hist = {}
    for _, _, h in res:
        for k, v in h.items():
            hist[k] = hist.get(k, 0) + v
    print(f'N={N} m={m}: W_m(N) = {best} ({float(best):.4f}); C(N,m) = {math.comb(N, m)}; '
          f'bound s_N >= {math.comb(N, m) / best if best else float("inf"):.4f}', flush=True)
    S, states, (kappa, hin, lin, Ts) = cfg
    print('  argmax S', S, 'states', states, 'kappa', kappa, 'F', hin, 'lin', lin)
    print('  its T sets:', [(T, str(w)) for T, w in Ts])
    print('  histogram top:', [(str(k), v) for k, v in sorted(hist.items(), key=lambda kv: -kv[0])[:8]])
