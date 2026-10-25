#!/usr/bin/env python3
"""Independent Q2 evaluation by explicit signed connected-order enumeration."""
from collections import deque
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from pathlib import Path
import hashlib
import json
import time

HERE = Path(__file__).absolute().parent


@lru_cache(None)
def tree_data(edges):
    vertices = sorted({v for edge in edges for v in edge})
    graph = {v: set() for v in vertices}
    for u, v in edges:
        graph[u].add(v)
        graph[v].add(u)
    counts = dict.fromkeys(vertices, 0)
    for order in permutations(vertices):
        seen = {order[0]}
        for v in order[1:]:
            if not graph[v] & seen:
                break
            seen.add(v)
        else:
            inversions = sum(u > v for i, u in enumerate(order) for v in order[i + 1:])
            counts[order[0]] += (-1) ** inversions
    distances = {}
    for root in vertices:
        distance = {root: 0}
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in graph[u]:
                if v not in distance:
                    distance[v] = distance[u] + 1
                    queue.append(v)
        distances[root] = distance
    return vertices, graph, counts, distances


def score(unit):
    oriented = set(map(tuple, unit['edges']))
    vertices, graph, counts, distances = tree_data(tuple(sorted(tuple(sorted(e)) for e in oriented)))
    root = unit['root']
    epsilon = 1
    for u, v in oriented:
        epsilon *= 1 if distances[root][u] > distances[root][v] else -1
    B = sum((-1) ** distances[root][v] * len(graph[v]) * counts[v] for v in vertices)
    D1 = G1 = H2 = 0
    for u in vertices:
        for v in vertices:
            distance = distances[u][v]
            product = counts[u] * counts[v]
            D1 += distance * product
            G1 += distance * (len(graph[u]) + len(graph[v])) * product
            H2 += distance ** 2 * len(graph[u]) * len(graph[v]) * product
    return epsilon * (2 * B ** 2 + Fraction(3, 2) * D1 - Fraction(5, 4) * G1 + H2)


def main():
    started = time.monotonic()
    inventory = HERE / 'overnight_uniform_q9_inventory.json'
    proposal = HERE / 'overnight_uniform_endpoint_q2.json'
    units = json.loads(inventory.read_text())['units']
    p = json.loads(proposal.read_text())['results'][1]['proposals'][0]
    values = {index: score(units[int(index)]) for index in p['integer_proposal']}
    pairing = sum(int(weight) * values[index] for index, weight in p['integer_proposal'].items())
    assert p['target_coefficient'] == 0
    assert pairing == -448
    result = dict(status='PASS', independent_method='explicit signed connected growth orders',
                  score_pairing=str(pairing), scores={i: str(v) for i, v in values.items()},
                  input_sha256={f.name: hashlib.sha256(f.read_bytes()).hexdigest() for f in (inventory, proposal)},
                  seconds=time.monotonic() - started)
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'score_pairing': str(pairing), 'seconds': result['seconds']}))


if __name__ == '__main__':
    main()
