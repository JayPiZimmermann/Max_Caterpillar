#!/usr/bin/env python3
"""Count complete matching-deficient function families before a long probe.

All unlabeled shapes, roots, and orientations are enumerated. Normalize by
kappa=outdegree+root marker, then quotient by graph automorphisms. Budget
300 seconds; no rank or spanning claim is made by this inventory.
"""
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time

import networkx as nx


def main(m):
    assert m >= 5 and m % 2 == 1
    start = time.monotonic()
    n = m-1
    threshold = n//2-1
    records = []
    reps = []
    raw = 0
    for shape, g0 in enumerate(nx.nonisomorphic_trees(n)):
        graph = nx.convert_node_labels_to_integers(g0, first_label=1)
        nodes = tuple(sorted(graph))
        edges = tuple(sorted(tuple(sorted(e)) for e in graph.edges()))
        matching = len(nx.max_weight_matching(graph, maxcardinality=True))
        if matching > threshold:
            records.append(dict(shape=shape, edges=edges, matching=matching,
                                allowed=False, function_orbits=0))
            continue
        autos = list(nx.algorithms.isomorphism.GraphMatcher(graph, graph).isomorphisms_iter())
        seen = set()
        before = len(reps)
        for root in nodes:
            for bits in itertools.product((0, 1), repeat=n-1):
                assert time.monotonic()-start < 300
                oriented = tuple((u, v) if bit else (v, u)
                                 for (u, v), bit in zip(edges, bits))
                kappa = {v: int(v == root) for v in nodes}
                for u, v in oriented:
                    kappa[u] += 1
                raw += 1
                key = min(tuple(kappa[a[v]] for v in nodes) for a in autos)
                if key in seen:
                    continue
                seen.add(key)
                cuts = []
                for u, v in oriented:
                    h = graph.copy()
                    h.remove_edge(u, v)
                    side = set(nx.node_connected_component(h, u))
                    sign = 1
                    if root in side:
                        side = set(nodes)-side
                        sign = -1
                    cuts.append((tuple(sorted(side)), sign))
                reps.append(dict(shape=shape, root=root, edges=oriented,
                                 kappa=[kappa[v] for v in nodes], cuts=cuts))
        records.append(dict(shape=shape, edges=edges, matching=matching,
                            allowed=True, automorphisms=len(autos),
                            function_orbits=len(reps)-before))
        print('SHAPE', shape, 'matching', matching, 'orbits', len(reps)-before,
              'seconds', round(time.monotonic()-start, 3), flush=True)
    result = dict(arity=m, max_matching=threshold, shapes=records,
                  raw_allowed_units=raw, function_orbits=len(reps),
                  representatives=reps, elapsed_seconds=time.monotonic()-start,
                  budget_seconds=300, status='COMPLETE_ENUMERATION_NO_SPAN_CLAIM',
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    out = Path(__file__).with_name(f'overnight_lower_inventory_{m}.json')
    out.write_text(json.dumps(result, indent=2)+'\n')
    print('DONE', {k: v for k, v in result.items() if k not in ('shapes', 'representatives')}, flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv)>1 else 9)
