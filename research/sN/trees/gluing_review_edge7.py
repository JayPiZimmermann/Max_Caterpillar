#!/usr/bin/env python3
"""Independent coverage, normalization and first-row audit of BFS edge shifts."""
from collections import deque
from fractions import Fraction as Q
import hashlib
import itertools
import json
import math
from pathlib import Path
import time

import numpy as np

from gluing_review import pruefer_tree
from gluing_review_gates import dfs_value_mod
from exponential_families_batch import engine, evaluate

HERE = Path(__file__).parent


def is_bfs_in_either_direction(tree):
    for sign, shift in itertools.product((-1, 1), range(6)):
        adjacency = [[] for _ in range(6)]
        for u, v in tree:
            u, v = (sign * u + shift) % 6, (sign * v + shift) % 6
            adjacency[u].append(v)
            adjacency[v].append(u)
        queue, seen, order = deque([0]), {0}, []
        while queue:
            v = queue.popleft()
            order.append(v)
            for w in sorted(adjacency[v]):
                if w not in seen:
                    seen.add(w)
                    queue.append(w)
        if order == list(range(6)):
            return True
    return False


def main():
    started = time.monotonic()
    source = HERE / 'exponential_batch_bfs_edge_7.json'
    gate_source = HERE / 'exponential_kernel_bfs_edge_7.json'
    data, gate = json.loads(source.read_text()), json.loads(gate_source.read_text())
    assert gate['status'] == 'ALL_EXACT_KERNEL_IDENTITIES_VERIFIED'
    assert gate['source_sha256'] == hashlib.sha256(source.read_bytes()).hexdigest()
    assert gate['checker_sha256'] == hashlib.sha256((HERE / 'exponential_kernel_gate.py').read_bytes()).hexdigest()
    orbits = [[(tuple(h), tuple(map(tuple, es))) for h, es in orbit] for orbit in data['orbits']]
    stored = {key for orbit in orbits for key in orbit}
    assert len(stored) == sum(map(len, orbits))
    trees = []
    for code in itertools.product(range(6), repeat=4):
        tree = tuple(sorted(tuple(sorted(e)) for e in pruefer_tree(6, code)))
        if is_bfs_in_either_direction(tree):
            trees.append(tree)
    assert len(trees) == len(set(trees)) == 444
    independent = set()
    for apex in range(7):
        vertices = [v for v in range(7) if v != apex]
        for tree in trees:
            edges = tuple((vertices[u], vertices[v]) for u, v in tree)
            h = [0] * 7
            h[apex] = -1
            for v in vertices:
                h[v] = 1 - sum(u == v for u, w in edges)
            independent.add((tuple(h), edges))
            for u, v in edges:
                for sign in (-1, 1):
                    shifted = h.copy()
                    shifted[u] += sign
                    shifted[v] -= sign
                    independent.add((tuple(shifted), edges))
    assert independent == stored
    free, proposals = data['kernel_free_columns'], data['kernel_proposals']
    assert len(free) == len(set(free)) == len(proposals) == 5
    assert sorted(gate['passed_indices']) == list(range(5))
    for f, raw in zip(free, proposals):
        vector = {int(j): Q(c) for j, c in raw}
        assert len(vector) == len(raw)
        assert [vector.get(j, Q(0)) for j in free] == [Q(j == f) for j in free]
    point, prime = data['points'][0], data['prime']
    row = [sum(dfs_value_mod(key, point, prime) for key in orbit) % prime for orbit in orbits]
    row.append(pow(math.prod(point) % prime, -1, prime))
    keys, offsets, forms, incidence, apices = engine(7, orbits)
    batch, unused = evaluate(7, [point], offsets, forms, incidence, apices)
    assert row == list(map(int, batch[0]))
    for raw in proposals:
        value = sum(row[j] * Q(c).numerator * pow(Q(c).denominator, -1, prime) for j, c in raw)
        assert value % prime == 0
    result = dict(status='INDEPENDENT_BFS_EDGE7_COVERAGE_AND_FIRST_ROW_PASS',
                  tree_count_per_apex=len(trees), full_units=len(stored), orbit_columns=len(orbits),
                  independently_normalized_exact_kernel_relations=5,
                  ordinary_rank_upper=len(orbits) - len(free), augmented_rank_lower=gate['augmented_rank_lower_from_modular_receipt'],
                  independent_first_row_entries=len(row),
                  first_row_uint32_sha256=hashlib.sha256(np.array(row, dtype=np.uint32).tobytes()).hexdigest(),
                  kernel_identities_rechecked_symbolically=False, large_modular_rank_repeated=False,
                  source=source.name, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  gate_source=gate_source.name, gate_sha256=hashlib.sha256(gate_source.read_bytes()).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  dfs_checker_sha256=hashlib.sha256((HERE / 'gluing_review_gates.py').read_bytes()).hexdigest(),
                  elapsed_seconds=time.monotonic() - started)
    (HERE / 'gluing_review_bfs_edge7.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
