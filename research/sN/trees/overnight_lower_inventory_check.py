#!/usr/bin/env python3
"""Independent complete eight-vertex matching-family inventory check.

Uses only the standard library: Prüfer sequences, unrooted coloured-tree
canonical forms, and brute-force disjoint edge sets. No graph-library
enumeration, matching, or isomorphism routine from the producer is used.
Budget 120 seconds. This checks a finite domain, not a separation theorem.
"""
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def adjacency(n, edges):
    adj = [0]*n
    for u, v in edges:
        assert u != v and not (adj[u] >> v & 1)
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    reached = 1
    for _ in range(n):
        for u in tuple(vertices(reached)):
            reached |= adj[u]
    assert reached == (1 << n)-1 and len(edges) == n-1
    return adj


def canonical(adj, colours=None):
    n = len(adj)
    if colours is None:
        colours = [0]*n
    remaining = (1 << n)-1
    while remaining.bit_count() > 2:
        leaves = sum(1 << i for i in vertices(remaining)
                     if (adj[i] & remaining).bit_count() <= 1)
        assert leaves
        remaining ^= leaves

    def rooted(v, parent):
        return (colours[v], tuple(sorted(rooted(w, v) for w in vertices(adj[v])
                                        if w != parent)))

    return min(rooted(v, -1) for v in vertices(remaining))


def from_prufer(seq, n):
    degree = [1]*n
    for v in seq:
        degree[v] += 1
    leaves = sum(1 << i for i in range(n) if degree[i] == 1)
    adj = [0]*n
    for v in seq:
        bit = leaves & -leaves
        u = bit.bit_length()-1
        leaves ^= bit
        adj[u] |= 1 << v
        adj[v] |= bit
        degree[v] -= 1
        if degree[v] == 1:
            leaves |= 1 << v
    u, v = tuple(vertices(leaves))
    adj[u] |= 1 << v
    adj[v] |= 1 << u
    return adj


def main(m):
    started = time.monotonic()
    path = Path(__file__).with_name(f'overnight_lower_inventory_{m}.json')
    data = json.loads(path.read_text())
    n = m-1
    assert m == data['arity'] == 9
    assert data['max_matching'] == n//2-1
    shapes = {}
    by_id = {}
    for rec in data['shapes']:
        edges = tuple((u-1, v-1) for u, v in rec['edges'])
        adj = adjacency(n, edges)
        key = canonical(adj)
        assert key not in shapes
        perfect = any(len({v for edge in chosen for v in edge}) == n
                      for chosen in itertools.combinations(edges, n//2))
        assert rec['allowed'] == (not perfect)
        shapes[key] = dict(record=rec, adj=adj, edges=edges, count=0)
        by_id[rec['shape']] = shapes[key]
    total = 0
    for seq in itertools.product(range(n), repeat=n-2):
        assert time.monotonic()-started < 120
        key = canonical(from_prufer(seq, n))
        assert key in shapes
        shapes[key]['count'] += 1
        total += 1
    assert all(s['count'] > 0 for s in shapes.values())
    print('PRUFER', total, 'trees', len(shapes), 'shapes',
          'seconds', round(time.monotonic()-started, 3), flush=True)

    raw = unique = 0
    actual_by_shape = {shape: [] for shape in by_id}
    for unit in data['representatives']:
        state = by_id[unit['shape']]
        assert state['record']['allowed']
        root = unit['root']-1
        assert 0 <= root < n
        oriented = tuple((u-1, v-1) for u, v in unit['edges'])
        assert adjacency(n, oriented) == state['adj']
        kappa = [int(v == root) for v in range(n)]
        for u, v in oriented:
            kappa[u] += 1
        assert kappa == unit['kappa']
        actual_by_shape[unit['shape']].append(canonical(state['adj'], kappa))
    for shape, state in by_id.items():
        expected = set()
        if state['record']['allowed']:
            for root in range(n):
                for bits in itertools.product((0, 1), repeat=n-1):
                    kappa = [int(v == root) for v in range(n)]
                    for (u, v), bit in zip(state['edges'], bits):
                        kappa[u if bit else v] += 1
                    expected.add(canonical(state['adj'], kappa))
                    raw += 1
        actual = actual_by_shape[shape]
        assert len(actual) == len(set(actual))
        assert set(actual) == expected
        assert len(actual) == state['record']['function_orbits']
        unique += len(expected)
    assert unique == data['function_orbits']
    assert raw == data['raw_allowed_units']
    result = dict(status='INDEPENDENT_COMPLETE_INVENTORY_CHECK_PASS',
                  arity=m, all_labelled_trees=total, all_shapes=len(shapes),
                  allowed_shapes=sum(s['record']['allowed'] for s in shapes.values()),
                  allowed_labelled_trees=sum(s['count'] for s in shapes.values()
                                            if s['record']['allowed']),
                  raw_allowed_root_orientation_choices=raw, function_orbits=unique,
                  seconds=time.monotonic()-started, budget_seconds=120,
                  inventory_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Exact finite family coverage only; no rank or separation result')
    out = Path(__file__).with_name(f'overnight_lower_inventory_check_{m}.json')
    out.write_text(json.dumps(result, indent=2)+'\n')
    print('DONE', json.dumps(result), flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv)>1 else 9)
