#!/usr/bin/env python3
"""Independent check of the spine/valley formula (research/sN/polytope/spinecheck.py).
For every unit of arity N and every hinge component C (spine run s_1..s_L of the
caterpillar spine plus pendant hinge leaves), recompute P_C(x) as
  sum over X subset spine-vertices of C (leaves follow their spine vertex):
    validity: every vertex with lambda >= 2 in X; each maximal outside run R has
      exactly one 'min' (non-root lambda=1, or root lambda=0) and all other
      outside vertices non-min (non-root lambda=0, root lambda=-1);
      (b): S-vertex with kappa = 0 has an S-neighbour;
    weight x^{|S|} * prod_R prod_{v in piece} 1/h(v)  (hook product of the valley),
and compare with genfun.comp_poly (brute-force order counting).  Also checks
lambda_v >= 0 for non-root C vertices, lambda >= -1 at the root, kappa(leaf)=0,
and the per-component bound Q_C(1/4) = 4^{-D} P_C(1/4) <= 1.  Usage: spinecheck.py N"""
import sys
from fractions import Fraction as Fr
import genfun as gf

N = int(sys.argv[1])
r = N - 2
bad = 0
checked = 0
maxQ = Fr(0)
for S, states, edges, last in gf.all_units(N):
    kappa, hin = gf.unit_data(N, edges, last, states)
    parent = {c: p for (p, c) in edges}
    spine = {1} | {i + 1 for i in S}
    lin_children = {v: 0 for v in range(N)}
    parent_lin = {v: False for v in range(N)}
    for (p, c), s in zip(edges, states):
        if s == 1:
            lin_children[p] += 1; parent_lin[c] = True
    lam = {v: lin_children[v] + (v == last) - (v == 0) - parent_lin[v] for v in range(N)}
    comps, nbr = gf.components(N, hin)
    for comp in comps:
        if len(comp) == 1:
            continue
        cs = set(comp)
        root = [v for v in comp if parent.get(v) not in cs][0]
        sp = sorted([v for v in comp if v in spine])
        leaves = [v for v in comp if v not in spine]
        # structural facts
        assert root in spine and root == sp[0]
        assert all(kappa[l] == 0 for l in leaves), 'leaf kappa'
        for v in comp:
            cd = sum(1 for u in nbr[v] if parent.get(u) == v)
            assert kappa[v] == cd + lam[v]
            assert lam[v] >= (-1 if v == root else 0)
        L = len(sp)
        lv = {v: [l for l in leaves if parent[l] == v] for v in sp}
        poly = [Fr(0)] * (len(comp) + 1)
        for mask in range(1 << L):
            X = [sp[i] for i in range(L) if mask >> i & 1]
            Sset = set(X) | {l for v in X for l in lv[v]}
            ok = all(v in Sset for v in comp if lam[v] >= 2)
            # (b)
            for t in Sset:
                if kappa[t] == 0 and not any(u in Sset for u in nbr[t]):
                    ok = False
            if not ok:
                continue
            # runs
            w = Fr(1)
            i = 0
            while i < L and ok:
                if mask >> i & 1:
                    i += 1; continue
                j = i
                while j < L and not mask >> j & 1:
                    j += 1
                run = sp[i:j]
                mins = []
                for v in run:
                    if v == root:
                        if lam[v] == 0: mins.append(v)
                        elif lam[v] != -1: ok = False
                    else:
                        if lam[v] == 1: mins.append(v)
                        elif lam[v] != 0: ok = False
                if len(mins) != 1:
                    ok = False
                    break
                m = run.index(mins[0])
                size = lambda seg: sum(1 + len(lv[v]) for v in seg)
                for q, v in enumerate(run):
                    if q < m: h = size(run[:q + 1])
                    elif q > m: h = size(run[q:])
                    else: h = size(run)
                    w /= h
                i = j
            if ok:
                poly[len(Sset)] += w
        ref = list(gf.comp_poly(gf.canon(comp, nbr, kappa)))
        checked += 1
        if poly != ref:
            bad += 1
            if bad < 5:
                print('MISMATCH', S, states, comp, poly, ref)
        D = sum(kappa[v] for v in comp) - (len(comp) - 1)
        Q = Fr(1, 4) ** D * sum(c * Fr(1, 4) ** i for i, c in enumerate(ref))
        maxQ = max(maxQ, Q)
print(f'N={N}: components checked {checked}, mismatches {bad}, max Q_C(1/4) = {maxQ} ({float(maxQ):.4f})')
