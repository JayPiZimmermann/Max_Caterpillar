#!/usr/bin/env python3
"""Polynomial-orbit families of tree units (research/sN/trees).

A type: apex a, centre c, k special vertices s_1..s_k, and the remaining N-2-k labels as
GENERIC leaves of c, all with one common state.  Special vertices form, with c, a tree
(each s_i attached to c or to an earlier s_j) with arbitrary edge states.  Edge states:
'o' omitted, 'l+' linear +(y_child - y_parent), 'l-' linear -(...), 'h+' relu(y_child - y_parent),
'h-' relu(y_parent - y_child).  Head vertex r in {c, s_1..s_k}.  Unit:
    relu(y_r - y_a + sum_lin eps (y_child - y_parent) + sum_hinge relu(eps (y_child - y_parent))).
These are faces of class-G tree pyramids (tree: c joined to generic leaves and the special tree).
Orbit sum over S_N has N!/(N-2-k)! terms: polynomial in N for fixed k.
Test: is max_N in span(orbit sums of all types with <= k specials) + span(aux orbit sums)?
(max_N and the aux span are S_N-invariant, so this is equivalent to max_N being in the span of
all units of these types.)  Instrument: evaluation rank mod p at random integer points.
Usage: sym_span.py N k [Rgen]
"""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from pn_test import rank_mod_p

STATES = ['o', 'l+', 'l-', 'h+', 'h-']


def special_trees(k):
    """parent lists: parent[i] in {-1 (=c)} U {0..i-1}."""
    for par in itertools.product(*[range(-1, i) for i in range(k)]):
        yield par


def types(k_max):
    out = []
    for k in range(k_max + 1):
        for par in special_trees(k):
            for st in itertools.product(STATES, repeat=k):
                for gst in STATES:
                    for r in range(-1, k):
                        out.append((k, par, st, gst, r))
    return out


def edge_term(st, child, parent):
    """returns (linear coefficient vector contribution as dict, hinge (i,j) meaning relu(y_i - y_j))"""
    if st == 'o':
        return {}, None
    if st == 'l+':
        return {child: 1, parent: -1}, None
    if st == 'l-':
        return {child: -1, parent: 1}, None
    if st == 'h+':
        return {}, (child, parent)
    return {}, (parent, child)


def eval_type_orbit(N, typ, X):
    k, par, st, gst, r = typ
    tot = np.zeros(len(X), dtype=np.int64)
    for lab in itertools.permutations(range(N), k + 2):
        a, c = lab[0], lab[1]
        sp = lab[2:]
        gen = [x for x in range(N) if x not in lab]
        lin = np.zeros(N, dtype=np.int64)
        rr = c if r == -1 else sp[r]
        lin[rr] += 1; lin[a] -= 1
        hinges = []
        def add(stt, child, parent):
            d, h = edge_term(stt, child, parent)
            for t, cf in d.items():
                lin[t] += cf
            if h is not None:
                hinges.append(h)
        for i in range(k):
            parent = c if par[i] == -1 else sp[par[i]]
            add(st[i], sp[i], parent)
        for g in gen:
            add(gst, g, c)
        s = X @ lin
        for (i, j) in hinges:
            s = s + np.maximum(X[:, i] - X[:, j], 0)
        tot += np.maximum(s, 0)
    return tot


def main():
    N, k = int(sys.argv[1]), int(sys.argv[2])
    T = types(k)
    rng = np.random.default_rng(3)
    npts = len(T) + 60
    X = rng.integers(-10**3, 10**3, size=(npts, N))
    cols = [eval_type_orbit(N, t, X) for t in T]
    aux = sum(np.maximum(X[:, i] - X[:, j], 0) for i in range(N) for j in range(N) if i != j)
    lin = X.sum(axis=1)
    mx = X.max(axis=1)
    B = np.stack(cols + [aux, lin], axis=1)
    r1 = rank_mod_p(B)
    r2 = rank_mod_p(np.concatenate([B, mx[:, None]], axis=1))
    print(f'N={N} k<={k}: {len(T)} types, rank {r1}, with max {r2} -> max {"NOT in" if r2 > r1 else "IN"} span', flush=True)


if __name__ == '__main__':
    main()
