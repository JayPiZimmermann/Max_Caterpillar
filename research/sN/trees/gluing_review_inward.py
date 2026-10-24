#!/usr/bin/env python3
"""Exact N=5 obstruction for all inward-oriented canonical tree units.

All S5 label permutations give two shape columns (path and star). Three
generic rational evaluations give a nonsingular augmented 3-by-3 matrix.
This is independent of the root agent's dihedral modular calculation.
"""
from fractions import Fraction as Q
import hashlib
import itertools
import json
import math
from pathlib import Path

from gluing_review import kernel, pruefer_tree


def oriented_to_root(vertices, edges, root):
    adjacency = {v: [] for v in vertices}
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    result = []

    def visit(v, parent):
        for child in adjacency[v]:
            if child != parent:
                result.append((child, v))
                visit(child, v)

    visit(root, None)
    return result


def root_controls():
    count = 0
    degree_types = set()
    for code in itertools.product(range(4), repeat=2):
        edges = pruefer_tree(4, code)
        degrees = [sum(v in e for e in edges) for v in range(4)]
        degree_types.add(tuple(sorted(degrees)))
        for root in range(4):
            directed = oriented_to_root(range(4), edges, root)
            kappa = [int(v == root) + sum(u == v for u, w in directed) for v in range(4)]
            assert kappa == [1] * 4
            for x in itertools.product((-2, 0, 3), repeat=4):
                direct = x[root] + sum(max(0, x[u] - x[v]) for u, v in directed)
                symmetric = sum(max(x[u], x[v]) for u, v in edges)
                symmetric -= sum((degrees[v] - 1) * x[v] for v in range(4))
                assert direct == symmetric
                count += 1
    assert degree_types == {(1, 1, 2, 2), (1, 1, 1, 3)}
    return count


def determinant3(matrix):
    a, b, c = matrix
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def deletion_controls():
    """Exact CPWL directional derivatives, separately from the deletion formula."""
    def M(vertices, edges, x):
        return (sum(max(x[u], x[v]) for u, v in edges)
                - sum((sum(v in e for e in edges) - 1) * x[v] for v in vertices))

    def partial(vertices, edges, apex, direction, x):
        base = M(vertices, edges, direction) - direction[apex]
        derivative = -x[apex]
        for u, v in edges:
            derivative += (x[u] if direction[u] > direction[v] else
                           x[v] if direction[v] > direction[u] else max(x[u], x[v]))
        derivative -= sum((sum(v in e for e in edges) - 1) * x[v] for v in vertices)
        return derivative if base > 0 else 0 if base < 0 else max(0, derivative)

    count = 0
    vertices, apex = set(range(4)), 4
    for code in itertools.product(range(4), repeat=2):
        edges = pruefer_tree(4, code)
        for v in range(5):
            direction = [int(j == v) * -1 for j in range(5)]
            opposite = [-t for t in direction]
            for x in itertools.product((-1, 0, 2), repeat=5):
                actual = partial(vertices, edges, apex, direction, x) - partial(vertices, edges, apex, opposite, x)
                if v == apex:
                    expected = M(vertices, edges, x) - x[v]
                else:
                    neighbours = [q if p == v else p for p, q in edges if v in (p, q)]
                    if len(neighbours) >= 2:
                        expected = sum(x[w] for w in neighbours) - len(neighbours) * x[v]
                    else:
                        p, = neighbours
                        smaller_edges = [edge for edge in edges if v not in edge]
                        smaller_M = M(vertices - {v}, smaller_edges, x)
                        smaller_U = max(0, smaller_M - x[apex])
                        expected = smaller_U - smaller_M + x[p] - x[v] + x[apex]
                assert actual == expected
                count += 1
    return count


def main():
    controls = root_controls()
    derivative_controls = deletion_controls()
    shapes = [dict(name='path', oriented_edges=[(2, 1), (3, 2), (4, 3)]),
              dict(name='star', oriented_edges=[(2, 1), (3, 1), (4, 1)])]
    frequencies = [(1, 2, 3, 4, -10), (1, 2, 4, 8, -15), (1, 3, 9, 27, -40)]
    matrix = []
    for om in frequencies:
        assert sum(om) == 0
        # All denominators are sums of proper nonempty frequency subsets.
        for mask in range(1, (1 << 5) - 1):
            assert sum(om[j] for j in range(5) if mask >> j & 1)
        row = []
        for shape in shapes:
            total = Q(0)
            for pi in itertools.permutations(range(5)):
                assigned = {j: om[pi[j]] for j in range(5)}
                a = assigned[0]
                total += -a * kernel(range(1, 5), shape['oriented_edges'], assigned, a, 1)
            row.append(total)
        row.append(Q(1, math.prod(om)))
        matrix.append(row)
    determinant = determinant3(matrix)
    assert determinant == Q(-108076159, 19163354302226534400)
    result = dict(status='EXACT_ALL_INWARD_TREE_TOP_OBSTRUCTION', inputs=5,
                  domain='All labelled trees, every apex and head root, every hinge directed child-to-parent toward the head root',
                  additional_lower_dimensional_faces=True,
                  mathematical_boundary='N=5 base obstruction; the reviewed opposite-face deletion proof propagates exclusion to every N>=5, but not to arbitrary edge orientations',
                  shape_columns=shapes, full_permutation_sum=True,
                  frequencies=frequencies,
                  augmented_matrix=[[str(v) for v in row] for row in matrix],
                  augmented_determinant=str(determinant),
                  exact_root_independence_controls=controls,
                  exact_opposite_derivative_deletion_controls=derivative_controls,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  kernel_source_sha256=hashlib.sha256(Path(__file__).with_name('gluing_review.py').read_bytes()).hexdigest())
    dest = Path(__file__).with_name('gluing_review_inward_5.json')
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
