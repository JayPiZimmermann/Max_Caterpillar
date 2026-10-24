#!/usr/bin/env python3
"""Exact deletion controls for inward units with a bounded-path linear shift."""
from collections import deque
import hashlib
import itertools
import json
from pathlib import Path
import random

from exponential_families import breadth_first
from gluing_review import pruefer_tree


def M(vertices, edges, x):
    return (sum(max(x[u], x[v]) for u, v in edges)
            - sum((sum(v in e for e in edges) - 1) * x[v] for v in vertices))


def partial(vertices, edges, apex, shift, u, x):
    base = M(vertices, edges, u) - u[apex] + sum(shift[j] * u[j] for j in vertices)
    d = -x[apex] + sum(shift[j] * x[j] for j in vertices)
    for i, j in edges:
        d += x[i] if u[i] > u[j] else x[j] if u[j] > u[i] else max(x[i], x[j])
    d -= sum((sum(v in e for e in edges) - 1) * x[v] for v in vertices)
    return d if base > 0 else 0 if base < 0 else max(0, d)


def main():
    rng = random.Random(24102497)
    count, nonlinear_nonleaf = 0, 0
    vertices, apex = set(range(4)), 4
    for code in itertools.product(range(4), repeat=2):
        edges = pruefer_tree(4, code)
        for plus, minus in itertools.permutations(vertices, 2):
            shift = [int(j == plus) - int(j == minus) for j in range(5)]
            for v in range(5):
                u = [-int(j == v) for j in range(5)]
                for _ in range(5):
                    x = [rng.randrange(-5, 6) for _ in range(5)]
                    actual = partial(vertices, edges, apex, shift, u, x) - partial(vertices, edges, apex, shift, [-t for t in u], x)
                    if v == apex:
                        expected = M(vertices, edges, x) - x[apex] + sum(shift[j] * x[j] for j in vertices)
                    else:
                        neighbours = [j if i == v else i for i, j in edges if v in (i, j)]
                        degree = len(neighbours)
                        remaining = vertices - {v}
                        forest = [e for e in edges if v not in e]
                        A = sum(max(x[i], x[j]) for i, j in forest)
                        A -= sum((sum(j in e for e in edges) - 1) * x[j] for j in remaining)
                        common = -x[apex] + sum(shift[j] * x[j] for j in vertices)
                        low = A + sum(x[j] for j in neighbours) - (degree - 1) * x[v] + common
                        high = A + x[v] + common
                        if degree >= 2:
                            if shift[v] == -1:
                                expected = low - max(0, high)
                                nonlinear_nonleaf += 1
                            elif shift[v] == 1 and degree == 2:
                                expected = max(0, low) - high
                                nonlinear_nonleaf += 1
                            else:
                                expected = sum(x[j] for j in neighbours) - degree * x[v]
                            # Any surviving outer unit has at most this support dimension.
                            assert len(forest) + 1 <= len(vertices) - 2
                        else:
                            p, = neighbours
                            smaller_M = M(remaining, forest, x)
                            restricted_shift = sum(shift[j] * x[j] for j in remaining)
                            if shift[v] == 0:
                                smaller = max(0, smaller_M - x[apex] + restricted_shift)
                                expected = smaller - high
                            elif shift[v] == 1:
                                expected = -high
                            else:
                                smaller = max(0, smaller_M - x[apex] + restricted_shift - x[p])
                                expected = low - smaller
                    assert actual == expected
                    count += 1
    leaf_checks = 0
    for n in range(2, 10):
        for edges in breadth_first(n):
            for removed in range(n):
                if sum(removed in e for e in edges) != 1:
                    continue
                remaining = [v for v in range(n) if v != removed]
                adjacency = {v: [] for v in remaining}
                for u, v in edges:
                    if removed not in (u, v):
                        adjacency[u].append(v)
                        adjacency[v].append(u)
                queue, seen, order = deque([remaining[0]]), {remaining[0]}, []
                while queue:
                    v = queue.popleft()
                    order.append(v)
                    for w in sorted(adjacency[v]):
                        if w not in seen:
                            seen.add(w)
                            queue.append(w)
                assert order == remaining
                leaf_checks += 1
    result = dict(status='EXACT_BOUNDED_PATH_SHIFT_DELETION_CONTROLS_PASS',
                  exact_directional_derivative_controls=count,
                  nonlinear_nonleaf_lower_dimension_controls=nonlinear_nonleaf,
                  bfs_leaf_deletion_controls=leaf_checks, bfs_vertex_counts=list(range(2, 10)),
                  consequence='Together with the reviewed deletion proof, BFS single-edge-shift exclusion at N=7 propagates to all N>=7',
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path(__file__).with_name('gluing_review_edge_deletion.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
