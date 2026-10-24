#!/usr/bin/env python3
"""Independent exact controls for rooted tree gluing and its closure boundary.

This verifies the stated rational identities, not uniform hierarchy sufficiency.
Uses SymPy only for the final two-vertex block residue certificate.
"""
from fractions import Fraction as Q
import hashlib
import itertools
import json
from pathlib import Path
import random
import time


def kernel(vertices, oriented_edges, frequencies, external, root):
    """Compute rooted subtree frequencies by an independent DFS traversal."""
    adjacency = {v: [] for v in vertices}
    oriented = set(oriented_edges)
    for u, v in oriented_edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    out = Q(1)
    seen = set()

    def visit(v, parent):
        nonlocal out
        assert v not in seen
        seen.add(v)
        total = frequencies[v]
        for child in adjacency[v]:
            if child == parent:
                continue
            q = visit(child, v)
            epsilon = 1 if (child, v) in oriented else -1
            out /= q * (q + epsilon * external)
            total += q
        return total

    visit(root, None)
    assert seen == set(vertices)
    return out


def component(vertices, edges, start, removed):
    pending, seen = [start], {start}
    while pending:
        v = pending.pop()
        for edge in edges:
            if frozenset(edge) == frozenset(removed):
                continue
            x, y = edge
            w = y if x == v else x if y == v else None
            if w is not None and w not in seen:
                seen.add(w)
                pending.append(w)
    return seen


def pruefer_tree(n, code):
    degree = [1] * n
    for v in code:
        degree[v] += 1
    edges = []
    for v in code:
        leaf = next(i for i, d in enumerate(degree) if d == 1)
        edges.append((leaf, v))
        degree[leaf] -= 1
        degree[v] -= 1
    edges.append(tuple(i for i, d in enumerate(degree) if d == 1))
    return edges


def check_join(n, edges, frequencies, external, root, bridge):
    vertices = set(range(n))
    A = component(vertices, edges, root, bridge)
    B = vertices - A
    assert A and B
    u, v = bridge if bridge[0] in A else bridge[::-1]
    b = sum(frequencies[w] for w in B)
    shifted = dict(frequencies)
    shifted[u] += b
    edges_A = [e for e in edges if set(e) <= A]
    edges_B = [e for e in edges if set(e) <= B]
    epsilon = 1 if bridge[0] in B else -1
    lhs = kernel(vertices, edges, frequencies, external, root)
    rhs = (kernel(A, edges_A, shifted, external, root)
           * kernel(B, edges_B, frequencies, external, v)
           / (b * (b + epsilon * external)))
    assert lhs == rhs


def residue_obstruction():
    import sympy as sp
    x, a, b = sp.symbols('x a b')
    y = b - x
    functions = [1 / (x * (x + a)), 1 / (x * (x - a)),
                 1 / (y * (y + a)), 1 / (y * (y - a)), 1 / (x * y)]
    poles = [-a, a, b + a, b - a, 0]
    matrix = sp.Matrix([[sp.cancel((x - pole) * f).subs(x, pole) for f in functions]
                        for pole in poles])
    matrix = matrix.applyfunc(sp.cancel)
    determinant = sp.factor(matrix.det())
    assert determinant == 1 / (a ** 4 * b)
    assert matrix[:4, 4] == sp.zeros(4, 1)
    assert matrix[:4, :4] == sp.diag(-1 / a, 1 / a, 1 / a, -1 / a)
    return dict(coefficient_field='Q(a,b)', variable='x', other_frequency='y=b-x',
                pole_rows=[str(p) for p in poles],
                augmented_residue_matrix=[[str(v) for v in matrix.row(i)] for i in range(5)],
                augmented_determinant=str(determinant),
                conclusion='1/(x*y) is outside the four rooted oriented two-vertex kernels over Q(a,b)')


def main():
    started = time.monotonic()
    count = 0
    for n in range(2, 5):
        frequencies = {v: 2 + 3 * v for v in range(n)}
        for code in itertools.product(range(n), repeat=n - 2):
            tree = pruefer_tree(n, code)
            for mask in range(1 << (n - 1)):
                edges = [e[::-1] if mask >> j & 1 else e for j, e in enumerate(tree)]
                for root in range(n):
                    for bridge in edges:
                        for external in (101, -sum(frequencies.values())):
                            check_join(n, edges, frequencies, external, root, bridge)
                            count += 1
    rng = random.Random(24102473)
    for n in range(5, 9):
        for _ in range(32):
            tree = pruefer_tree(n, [rng.randrange(n) for _ in range(n - 2)])
            edges = [e[::-1] if rng.randrange(2) else e for e in tree]
            frequencies = {v: rng.randrange(1, 1000) for v in range(n)}
            root, bridge = rng.randrange(n), rng.choice(edges)
            for external in (1000003, -sum(frequencies.values())):
                check_join(n, edges, frequencies, external, root, bridge)
                count += 1
    frequencies = {0: 2, 1: 3, 2: 5}
    actual = kernel({0, 1, 2}, [(1, 0), (2, 1)], frequencies, 7, 0)
    wrong_unshifted = kernel({0, 1}, [(1, 0)], frequencies, 7, 0) / (5 * 12)
    assert actual == Q(1, 7200) and wrong_unshifted == Q(1, 1800)
    boundary_actual = Q(1, 3 * (3 + 7))
    boundary_wrong = Q(1, 3 * (3 - 5))
    assert boundary_actual != boundary_wrong
    result = dict(status='EXACT_GLUING_AND_BOUNDARY_REVIEW_PASS', exact_gluing_controls=count,
                  exhaustive_nonapex_arities=[2, 3, 4], additional_nonapex_arities=[5, 6, 7, 8],
                  frequency_domains=['free external parameter', 'sum(omega)=-external'],
                  omitted_attachment_shift=dict(actual=str(actual), wrong=str(wrong_unshifted)),
                  replaced_external_parameter=dict(actual=str(boundary_actual), wrong=str(boundary_wrong)),
                  smallest_block_obstruction=residue_obstruction(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  elapsed_seconds=time.monotonic() - started)
    dest = Path(__file__).with_name('gluing_review_receipt.json')
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
