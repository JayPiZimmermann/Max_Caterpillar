#!/usr/bin/env python3
"""Full symmetric probe for canonical trees with at most one zero kappa.

Budget 120 seconds, at most max(80, orbit_count+30) frequency rows. The
finite-field ranks are DIAGNOSTICS ONLY. Includes every unlabeled shape,
all ordered defect/excess marks modulo automorphisms, and all labelings.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

import networkx as nx
import numpy as np

from dfs_review_fourier import points

HERE = Path(__file__).resolve().parent
PRIME = 1000003


def canonical_unit(G, excess, defect):
    root = excess
    distance = nx.single_source_shortest_path_length(G, defect)
    oriented = tuple(sorted((u,v) if distance[u] > distance[v] else (v,u)
                            for u,v in G.edges()))
    cuts = []
    for u,v in oriented:
        H = G.copy()
        H.remove_edge(u,v)
        side = set(nx.node_connected_component(H,u))
        sign = 1
        if root in side:
            side = set(G)-side
            sign = -1
        cuts.append((tuple(sorted(side)),sign))
    kappa = {v: int(v == root) for v in G}
    for u,v in oriented:
        kappa[u] += 1
    assert all(kappa[v] == 1+int(v == excess)-int(v == defect) for v in G)
    return dict(root=root, sink=defect, edges=oriented, cuts=cuts,
                excess=excess, defect=defect,
                zero_count=sum(z == 0 for z in kappa.values()))


def family(m):
    units = []
    shape_counts = []
    for shape, G0 in enumerate(nx.nonisomorphic_trees(m-1)):
        G = nx.convert_node_labels_to_integers(G0, first_label=1)
        autos = list(nx.algorithms.isomorphism.GraphMatcher(G,G).isomorphisms_iter())
        before = len(units)
        units.append(dict(canonical_unit(G,1,1),shape=shape))
        seen = set()
        for s in G:
            for t in G:
                if s == t:
                    continue
                key = min((a[s],a[t]) for a in autos)
                if key in seen:
                    continue
                seen.add(key)
                units.append(dict(canonical_unit(G,s,t),shape=shape))
        shape_counts.append(dict(shape=shape,edges=sorted(G.edges()),orbits=len(units)-before))
    return units,shape_counts


def closure_controls():
    units = cases = 0
    counts = {0:0,1:0,2:0}
    for n in range(2,8):
        for G0 in nx.nonisomorphic_trees(n):
            G = nx.convert_node_labels_to_integers(G0,first_label=1)
            E = tuple(G.edges())
            for root in G:
                for bits in itertools.product((0,1),repeat=n-1):
                    oriented = [(u,v) if b else (v,u) for (u,v),b in zip(E,bits)]
                    kappa = {v:int(v == root) for v in G}
                    for u,v in oriented:
                        kappa[u] += 1
                    assert min(kappa.values()) >= 0 and sum(kappa.values()) == n
                    d = sum(z == 0 for z in kappa.values())
                    units += 1
                    for leaf in G:
                        if G.degree(leaf) != 1:
                            continue
                        hub = next(iter(G[leaf]))
                        kl = kappa[leaf]
                        assert kl in (0,1,2)
                        counts[kl] += 1
                        cases += 1
                        if kl == 2:
                            assert root == leaf and (leaf,hub) in oriented
                            continue
                        root2 = hub if root == leaf else root
                        kap2 = {v:int(v == root2) for v in G if v != leaf}
                        for u,v in oriented:
                            if leaf not in (u,v):
                                kap2[u] += 1
                        d2 = sum(z == 0 for z in kap2.values())
                        if kl == 0:
                            assert kap2[hub] == kappa[hub]-1
                            assert d2 == d-1+int(kappa[hub] == 1)
                        else:
                            assert kap2[hub] == kappa[hub]
                            assert d2 == d
                        assert d2 <= d
    return dict(units=units,leaf_cases=cases,by_leaf_kappa=counts,
                status='EXACT_KAPPA_CLOSURE_CONTROLS_PASS')


def main(m):
    start = time.monotonic()
    controls = closure_controls()
    units,shape_counts = family(m)
    perms = np.array(list(itertools.permutations(range(m))),dtype=np.int64)
    cuts = [[(sum(1<<i for i in side),sign) for side,sign in u['cuts']] for u in units]
    needed = sorted({mask for es in cuts for mask,sign in es})
    inv = np.zeros(PRIME,dtype=np.int64)
    inv[1] = 1
    for j in range(2,PRIME):
        inv[j] = PRIME-(PRIME//j)*inv[PRIME%j]%PRIME
    bases = [{},{}]
    rows,accepted = [],[]
    limit = max(80,len(units)+30)

    def insert(row,basis):
        v = np.array(row,dtype=np.int64)%PRIME
        for j,b in sorted(basis.items()):
            v = (v-v[j]*b)%PRIME
        nz = np.flatnonzero(v)
        if len(nz):
            j = int(nz[0])
            basis[j] = v*inv[v[j]]%PRIME

    print('DOMAIN',m,'all shapes',len(shape_counts),'d<=1 orbits',len(units),
          'row cap',limit,'controls',controls,flush=True)
    for pt in points(m,1000):
        om = np.array(pt,dtype=np.int64)[perms]%PRIME
        apex = om[:,0]
        qtab = {mask:om[:,[i for i in range(m) if mask>>i&1]].sum(axis=1)%PRIME for mask in needed}
        numerator = np.ones(len(perms),dtype=np.int64)
        for _ in range(m-4):
            numerator = numerator*(-apex)%PRIME
        row = []
        for es in cuts:
            denominator = np.ones(len(perms),dtype=np.int64)
            for mask,sign in es:
                q = qtab[mask]
                denominator = denominator*q%PRIME
                denominator = denominator*((q+sign*apex)%PRIME)%PRIME
            if np.any(denominator == 0):
                break
            row.append(int((numerator*inv[denominator]%PRIME).sum()%PRIME))
        if len(row) != len(units):
            continue
        target = int(((-1)**(m-1)*inv[math.prod(pt)%PRIME])%PRIME)
        insert(row,bases[0])
        insert(row+[target],bases[1])
        rows.append(row+[target])
        accepted.append(pt)
        if len(rows)%10 == 0:
            print('ROWS',len(rows),'RANKS',*map(len,bases),'SECONDS',round(time.monotonic()-start,3),flush=True)
        if len(rows) >= limit or time.monotonic()-start >= 120:
            break
    data = dict(arity=m,defect_bound=1,prime=PRIME,orbits=len(units),
                shapes=shape_counts,rows=len(rows),modular_ranks=list(map(len,bases)),
                points=accepted,evaluations=rows,representatives=units,
                closure_controls=controls,budget_seconds=120,
                elapsed_seconds=time.monotonic()-start,status='MODULAR_DIAGNOSTIC_ONLY',
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (HERE/f'lower_defect_review_probe_{m}.json').write_text(json.dumps(data,indent=2)+'\n')
    print('DONE',{k:v for k,v in data.items() if k not in {'points','evaluations','representatives','shapes'}},flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv)>1 else 7)
