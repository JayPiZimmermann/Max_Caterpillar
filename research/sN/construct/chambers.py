"""Exact chamber evaluator for sums of neurons d*sigma(l.x + sum w_ij sigma(x_i - x_j)).
neuron = (d, l(list len N), {(i,j): w}).  Fractions allowed."""
import itertools
from fractions import Fraction as Fr
from math import gcd

def lin_on(N, rank, l, W):
    """rank: tuple pos->element (pos 0 = top). returns coefficient vector a."""
    pos = [0] * N
    for p, e in enumerate(rank): pos[e] = p
    a = [Fr(v) for v in l]
    for (i, j), w in W.items():
        if pos[i] < pos[j]: a[i] += w; a[j] -= w
    return a, pos

def classify(N, rank, a):
    """returns ('pos'|'neg'|'zero'|'cross', key, lam) using gap coords in this chamber."""
    tot = sum(a)
    D = []; s = Fr(0)
    for p in range(N - 1):
        s += a[rank[p]]; D.append(s)
    if tot != 0:
        return 'cross', ('x',) + tuple(D) + (tot,), None  # not translation invariant: treat as crossing
    pos = any(d > 0 for d in D); neg = any(d < 0 for d in D)
    if not pos and not neg: return 'zero', None, None
    if pos and not neg: return 'pos', None, None
    if neg and not pos: return 'neg', None, None
    first = next(d for d in D if d)
    key = tuple(d / abs(first) for d in D)
    sgn = 1 if first > 0 else -1
    key = tuple(sgn * k for k in key)  # first nonzero = +1
    lam = first  # g = lam * key.D (since key scaled by 1/first... ) 
    return 'cross', key, lam

def evaluate(N, neurons, extra=None):
    """Return (braidPL: bool, bad list, pieces dict rank->coef vector) for F = sum neurons (+ extra linear-on-chamber fn)."""
    bad = []; pieces = {}
    for rank in itertools.permutations(range(N)):
        groups = {}; piece = [Fr(0)] * N
        for d, l, W in neurons:
            a, pos = lin_on(N, rank, l, W)
            kind, key, lam = classify(N, rank, a)
            if kind == 'pos':
                for i in range(N): piece[i] += d * a[i]
            elif kind == 'cross':
                if lam is None: bad.append((rank, 'noninv')); continue
                g = groups.setdefault(key, [Fr(0), [Fr(0)] * N])
                g[0] += d * abs(lam)
                if lam < 0:
                    for i in range(N): g[1][i] += d * a[i]
        for key, (tot, lp) in groups.items():
            if tot != 0: bad.append((rank, key, tot))
            for i in range(N): piece[i] += lp[i]
        pieces[rank] = piece
    return len(bad) == 0, bad, pieces

def top_of(N, pieces, a=0):
    """top coefficient of a braid-PL function from chamber pieces (coefficient of x_a by below-set)."""
    others = [i for i in range(N) if i != a]
    tot = Fr(0)
    for k in range(N):
        for U in itertools.combinations(others, k):
            above = [i for i in others if i not in U]
            rank = tuple(above) + (a,) + tuple(U)
            tot += (-1) ** (N - 1 - k) * pieces[rank][a]
    return tot
