#!/usr/bin/env python3
"""Independent seven-label matching-separator checker, budget 1200 seconds.

Coverage uses Prüfer trees and brute-force disjoint edge triples rather than
the producer's maximum-matching routine. Arithmetic uses normalized heads
and positive-endpoint cuts rather than cuts away from the original head root.
No FLINT or linear-system solving is used here.
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

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
ROWS = HERE / 'overnight_lower_matching_rows_7.json'
CERT = HERE / 'overnight_lower_matching_separator_7.json'
BUDGET = 1200


def edge_key(graph):
    return tuple(sorted(tuple(sorted(e)) for e in graph.edges()))


def has_three_disjoint_edges(graph):
    return any(len(set(sum((tuple(e) for e in es), ()))) == 6
               for es in itertools.combinations(graph.edges(), 3))


def main():
    start = time.monotonic()
    data = json.loads(ROWS.read_text())
    cert = json.loads(CERT.read_text())
    assert cert['status'] == 'EXACT_FINITE_EVALUATION_SEPARATOR'
    assert cert['rows_sha256'] == hashlib.sha256(ROWS.read_bytes()).hexdigest()
    assert data['arity'] == cert['arity'] == 7
    assert data['max_matching'] == cert['max_matching'] == 2
    m = 7
    n = 6
    units = data['representatives']
    graphs = []
    for shape in data['shapes']:
        graph = nx.Graph()
        graph.add_nodes_from(range(1, m))
        graph.add_edges_from(shape['edges'])
        assert nx.is_tree(graph)
        assert (shape['matching'] >= 3) == has_three_disjoint_edges(graph)
        graphs.append(graph)
    prufer_count = allowed_prufer_count = 0
    for seq in itertools.product(range(n), repeat=n-2):
        graph = nx.from_prufer_sequence(seq)
        assert sum(nx.is_isomorphic(graph, h) for h in graphs) == 1
        prufer_count += 1
        allowed_prufer_count += not has_three_disjoint_edges(graph)

    raw_units = function_orbits = 0
    seen_units = set()
    for graph in graphs:
        nodes = tuple(sorted(graph))
        edges = edge_key(graph)
        actual_units = [(i, u) for i, u in enumerate(units)
                        if edge_key(nx.Graph(u['edges'])) == edges]
        if has_three_disjoint_edges(graph):
            assert not actual_units
            continue
        autos = list(nx.algorithms.isomorphism.GraphMatcher(graph, graph).isomorphisms_iter())

        def orbit_key(kappa):
            return min(tuple(kappa[a[v]] for v in nodes) for a in autos)

        expected = set()
        for root in nodes:
            for bits in itertools.product((0, 1), repeat=n-1):
                oriented = [(u, v) if bit else (v, u)
                            for (u, v), bit in zip(edges, bits)]
                kappa = {v: int(v == root) for v in nodes}
                for u, v in oriented:
                    kappa[u] += 1
                expected.add(orbit_key(kappa))
                raw_units += 1
        actual = set()
        for idx, unit in actual_units:
            assert unit['root'] in nodes
            assert len(unit['edges']) == n-1
            kappa = {v: int(v == unit['root']) for v in nodes}
            for u, v in unit['edges']:
                kappa[u] += 1
            actual.add(orbit_key(kappa))
            seen_units.add(idx)
        assert actual == expected
        function_orbits += len(expected)
    assert seen_units == set(range(len(units)))
    print('COVERAGE', prufer_count, 'labelled trees', allowed_prufer_count,
          'allowed labelled trees', raw_units, 'root/orientation choices',
          len(units), 'columns', function_orbits, 'function orbits', flush=True)

    normalized = []
    for unit in units:
        graph = nx.Graph(unit['edges'])
        edges = edge_key(graph)
        kappa = {v: int(v == unit['root']) for v in graph}
        for u, v in unit['edges']:
            kappa[u] += 1
        head = dict(kappa)
        for u, v in edges:
            head[u] -= 1
        head[0] = -1
        assert sum(head.values()) == 0
        factors = []
        for u, v in edges:
            cut_graph = graph.copy()
            cut_graph.remove_edge(u, v)
            side = set(nx.node_connected_component(cut_graph, u))
            shift = sum(head[x] for x in side)
            assert shift in (-1, 0, 1)
            factors.append((sum(1 << x for x in side), shift))
        normalized.append(factors)
    needed = sorted({mask for fs in normalized for mask, shift in fs})
    perms = np.array(list(itertools.permutations(range(m))), dtype=np.int64)
    verified_rows = []
    assert len(data['points']) == len(data['scales']) == len(data['integer_rows'])
    for idx, (pt, scale_text, stored) in enumerate(zip(
            data['points'], data['scales'], data['integer_rows'])):
        assert time.monotonic() - start < BUDGET
        scale = int(scale_text)
        om = np.array(pt, dtype=np.int64)[perms]
        apex = om[:, 0]
        nums = ((-apex)**(m-4)).tolist()
        qs = {mask: om[:, [i for i in range(m) if mask >> i & 1]].sum(axis=1)
              for mask in needed}
        bound = 2 * abs(pt[0])
        common = math.lcm(*range(1, bound+1))**(2*(m-2))
        assert common % scale == 0
        divisor = common // scale
        reconstructed = []
        for fs in normalized:
            denominator = np.ones(len(perms), dtype=object)
            for mask, shift in fs:
                q = qs[mask]
                left, right = q + shift*apex, q + (shift+1)*apex
                assert np.all(left != 0) and np.all(right != 0)
                assert np.max(np.abs(left)) <= bound
                assert np.max(np.abs(right)) <= bound
                denominator *= left * right
            raw = 0
            for num, den in zip(nums, denominator):
                quotient, remainder = divmod(common, int(den))
                assert remainder == 0
                raw += num * quotient
            value, remainder = divmod(raw, divisor)
            assert remainder == 0
            reconstructed.append(value)
        target, remainder = divmod(common, math.prod(pt))
        assert remainder == 0
        target *= (-1)**(m-1)
        target, remainder = divmod(target, divisor)
        assert remainder == 0
        reconstructed.append(target)
        assert reconstructed == list(map(int, stored))
        verified_rows.append(reconstructed)
        print('VERIFIED ROW', idx+1, 'seconds', round(time.monotonic()-start, 3), flush=True)

    weights = list(map(int, cert['scaled_row_weights']))
    assert len(weights) == len(verified_rows)
    assert all(sum(w*row[j] for w, row in zip(weights, verified_rows)) == 0
               for j in range(len(units)))
    target = sum(w*row[-1] for w, row in zip(weights, verified_rows))
    assert target == int(cert['target_value']) and target != 0
    receipt = dict(
        status='INDEPENDENT_EXACT_MATCHING_SEPARATOR_CHECK_PASS', arity=m,
        max_matching=2, labelled_trees=prufer_count,
        allowed_labelled_trees=allowed_prufer_count,
        root_orientation_choices=raw_units, orbit_columns=len(units),
        function_orbits=function_orbits, verified_rows=len(verified_rows),
        target_nonzero=True, independent_mechanisms=[
            'Pruefer shape coverage', 'brute-force disjoint edge triples',
            'all roots and orientations', 'normalized-head positive-endpoint cuts',
            'integer separator dot products'],
        rows_sha256=hashlib.sha256(ROWS.read_bytes()).hexdigest(),
        certificate_sha256=hashlib.sha256(CERT.read_bytes()).hexdigest(),
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        elapsed_seconds=time.monotonic()-start, budget_seconds=BUDGET,
        trust_boundary='Exact finite Fourier certificate plus mathematical bridge; not Lean')
    (HERE / 'overnight_lower_matching_check_7.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print('DONE', receipt, flush=True)


if __name__ == '__main__':
    main()
