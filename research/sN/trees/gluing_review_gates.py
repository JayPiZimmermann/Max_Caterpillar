#!/usr/bin/env python3
"""Independent bounded reviews of the hierarchy obstruction and edge-marked witness.

Writes only gluing_review_* receipts. Does not repeat the large rank computation.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

from gluing_review import pruefer_tree

HERE = Path(__file__).parent


def normalized(h, edges):
    h = list(h)
    out = []
    for u, v in edges:
        if u > v:
            h[u] += 1
            h[v] -= 1
            u, v = v, u
        out.append((u, v))
    return tuple(h), tuple(sorted(out))


def dfs_value_mod(key, point, prime):
    """General-head Fourier value via DFS, without the batch factor engine."""
    h, edges = key
    n = len(h)
    vertices = set(v for edge in edges for v in edge)
    apex, = set(range(n)) - vertices
    assert h[apex] == -1 and sum(h) == 0 and sum(point) == 0
    a = point[apex]
    oriented = set(edges)
    adjacency = {v: [] for v in vertices}
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    den = 1
    seen = set()

    def visit(v, parent):
        nonlocal den
        assert v not in seen
        seen.add(v)
        q, H = point[v], h[v]
        for child in adjacency[v]:
            if child == parent:
                continue
            qq, HH = visit(child, v)
            epsilon = 1 if (child, v) in oriented else -1
            first, second = (qq + a * HH) % prime, (qq + a * (HH + epsilon)) % prime
            assert first and second
            den = den * first * second % prime
            q += qq
            H += HH
        return q, H

    visit(min(vertices), None)
    assert seen == vertices
    return pow(-a % prime, n - 4, prime) * pow(den, -1, prime) % prime


def hierarchy_seven():
    import numpy as np
    from exponential_families_batch import engine, evaluate
    started = time.monotonic()
    source = HERE / 'exponential_batch_hierarchy_full_7.json'
    gate_source = HERE / 'exponential_kernel_hierarchy_full_7.json'
    data, gate = json.loads(source.read_text()), json.loads(gate_source.read_text())
    assert gate['status'] == 'ALL_EXACT_KERNEL_IDENTITIES_VERIFIED'
    assert gate['source_sha256'] == hashlib.sha256(source.read_bytes()).hexdigest()
    assert gate['checker_sha256'] == hashlib.sha256((HERE / 'exponential_kernel_gate.py').read_bytes()).hexdigest()
    orbits = [[(tuple(h), tuple(map(tuple, es))) for h, es in orbit] for orbit in data['orbits']]
    stored_keys = {key for orbit in orbits for key in orbit}
    assert len(stored_keys) == sum(map(len, orbits))
    # Independent tree characterization: contain either adjacent perfect matching.
    matchings = [{(0, 1), (2, 3), (4, 5)}, {(1, 2), (3, 4), (0, 5)}]
    trees = []
    for code in itertools.product(range(6), repeat=4):
        tree = tuple(sorted(tuple(sorted(e)) for e in pruefer_tree(6, code)))
        if any(matching <= set(tree) for matching in matchings):
            trees.append(tree)
    assert len(trees) == len(set(trees)) == 96
    independent_keys = set()
    for apex in range(7):
        vertices = [v for v in range(7) if v != apex]
        for tree in trees:
            mapped = [(vertices[u], vertices[v]) for u, v in tree]
            for root in vertices:
                h = [0] * 7
                h[apex], h[root] = -1, 1
                for mask in range(32):
                    oriented = [e[::-1] if mask >> j & 1 else e for j, e in enumerate(mapped)]
                    independent_keys.add(normalized(h, oriented))
    assert independent_keys == stored_keys
    # Verify the actual group-orbit partition, without the producer's permute().
    for orbit in orbits:
        h, edges = orbit[0]
        expected = set()
        for sign, shift in itertools.product((-1, 1), range(7)):
            pi = [(sign * j + shift) % 7 for j in range(7)]
            hh = [0] * 7
            for j, value in enumerate(h):
                hh[pi[j]] = value
            expected.add(normalized(hh, [(pi[u], pi[v]) for u, v in edges]))
        assert expected == set(orbit)
    free, proposals = data['kernel_free_columns'], data['kernel_proposals']
    assert len(free) == len(set(free)) == len(proposals) == 296
    assert sorted(gate['passed_indices']) == list(range(296))
    for f, raw in zip(free, proposals):
        relation = {int(j): Q(c) for j, c in raw}
        assert len(relation) == len(raw)
        assert all(0 <= j < len(orbits) for j in relation)
        assert [relation.get(j, Q(0)) for j in free] == [Q(j == f) for j in free]
    point, prime = data['points'][0], data['prime']
    assert prime == 1000000007
    row = [sum(dfs_value_mod(key, point, prime) for key in orbit) % prime for orbit in orbits]
    row.append((-1) ** 6 * pow(math.prod(point) % prime, -1, prime) % prime)
    keys, offsets, forms, incidence, apices = engine(7, orbits)
    batch_row, unused = evaluate(7, [point], offsets, forms, incidence, apices)
    assert row == list(map(int, batch_row[0]))
    for raw in proposals:
        value = 0
        for j, coefficient in raw:
            c = Q(coefficient)
            value += row[j] * c.numerator * pow(c.denominator, -1, prime)
        assert value % prime == 0
    result = dict(status='INDEPENDENT_HIERARCHY7_COVERAGE_AND_FIRST_ROW_PASS',
                  tree_count_per_apex=96, full_units=len(keys), orbit_columns=len(orbits),
                  exact_kernel_relations_independently_normalized=296,
                  all_kernel_gate_receipt_indices_present=True,
                  kernel_identities_rechecked_symbolically=False,
                  large_modular_rank_repeated=False,
                  ordinary_rank_upper=len(orbits) - len(free), augmented_rank_lower=gate['augmented_rank_lower_from_modular_receipt'],
                  independent_first_row_entries=len(row), first_point=point,
                  first_row_uint32_sha256=hashlib.sha256(np.array(row, dtype=np.uint32).tobytes()).hexdigest(),
                  source=source.name, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  exact_gate_source=gate_source.name, exact_gate_source_sha256=hashlib.sha256(gate_source.read_bytes()).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  elapsed_seconds=time.monotonic() - started)
    (HERE / 'gluing_review_hierarchy7.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


def edge_six():
    sys.path.insert(0, str(HERE / 'all_tree_dfs'))
    from complete_flags import pyramid, simplex, sub
    started = time.monotonic()
    source = HERE / 'exponential_batch_bfs_edge_6.json'
    data = json.loads(source.read_text())
    assert data['status'] == 'EXACT_TOP_IDENTITY'
    coefficients = list(map(Q, data['coefficient_proposal']))
    assert {c for c in coefficients if c} == {Q(-1, 6), Q(1, 6)}
    n = 6
    e = [tuple(int(i == j) for i in range(n)) for j in range(n)]
    residual = defaultdict(Q, {key: -Q(v) for key, v in simplex(tuple(e)).items()})
    orbits, units = 0, 0
    for c, orbit in zip(coefficients, data['orbits']):
        if not c:
            continue
        orbits += 1
        for h, edges in orbit:
            h, edges = tuple(h), tuple(map(tuple, edges))
            vertices = set(v for edge in edges for v in edge)
            apex, = set(range(n)) - vertices
            assert h[apex] == -1 and sum(h) == 0
            defects = {v: h[v] + sum(u == v for u, w in edges) - 1 for v in vertices}
            nonzero = {v: value for v, value in defects.items() if value}
            assert not nonzero or (sorted(nonzero.values()) == [-1, 1] and tuple(sorted(nonzero)) in edges)
            generators = tuple(sorted(sub(e[u], e[v]) for u, v in edges))
            for key, value in pyramid(h, generators).items():
                residual[key] += c * Q(value)
            units += 1
    assert orbits == 7 and units == 84
    assert not any(residual.values())
    result = dict(status='INDEPENDENT_COMPLETE_FLAG_IDENTITY_PASS', inputs=6,
                  family='BFS with reversal, inward unit plus at most one oriented edge shift',
                  nonzero_orbits=orbits, full_units=units, coefficients=['-1/6', '1/6'],
                  complete_flag_rows=len(residual), residual_nonzero_rows=0,
                  source=source.name, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  elapsed_seconds=time.monotonic() - started)
    (HERE / 'gluing_review_bfs_edge6.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('command', choices=['hierarchy7', 'edge6'])
    args = parser.parse_args()
    (hierarchy_seven if args.command == 'hierarchy7' else edge_six)()
