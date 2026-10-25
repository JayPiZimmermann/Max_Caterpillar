#!/usr/bin/env python3
"""Exact combinatorial controls for a head-exchange-compatible score.

The last control refutes descent through an exact root-slide identity.
No numerical Fourier sampling or external packages are used here.
"""
from fractions import Fraction
from itertools import permutations, product
from math import factorial
from pathlib import Path
import hashlib
import json
import time


def rooted_signed_counts(edges):
    vertices = sorted({v for e in edges for v in e})
    tree = {v: set() for v in vertices}
    for u, v in edges:
        tree[u].add(v)
        tree[v].add(u)

    def visit(v, parent):
        children = [visit(w, v) for w in sorted(tree[v]) if w != parent]
        sizes = [len(labels) for labels, _ in children]
        labels = [v] + [w for block, _ in children for w in block]
        if sum(s % 2 for s in sizes) > 1:
            return sorted(labels), 0
        shuffle = factorial(sum(sizes) // 2)
        for s in sizes:
            shuffle //= factorial(s // 2)
        sign = (-1) ** sum(labels[i] > labels[j]
                           for i in range(len(labels)) for j in range(i + 1, len(labels)))
        value = sign * shuffle
        for _, count in children:
            value *= count
        return sorted(labels), value

    return {v: visit(v, None)[1] for v in vertices}


def prufer_tree(code, n):
    degree = [1] * n
    for v in code:
        degree[v] += 1
    edges = []
    for v in code:
        w = next(i for i, d in enumerate(degree) if d == 1)
        edges.append((w, v))
        degree[w] -= 1
        degree[v] -= 1
    edges.append(tuple(i for i, d in enumerate(degree) if d == 1))
    return edges


def brute_signed_counts(edges):
    vertices = sorted({v for e in edges for v in e})
    tree = {v: set() for v in vertices}
    for u, v in edges:
        tree[u].add(v)
        tree[v].add(u)
    out = {v: 0 for v in vertices}
    for order in permutations(vertices):
        seen = {order[0]}
        for v in order[1:]:
            if not tree[v] & seen:
                break
            seen.add(v)
        else:
            out[order[0]] += (-1) ** sum(order[i] > order[j]
                                       for i in range(len(order)) for j in range(i + 1, len(order)))
    return out


def matching_number(edges):
    best = 0
    for mask in range(1 << len(edges)):
        chosen = [e for i, e in enumerate(edges) if mask >> i & 1]
        if len({v for e in chosen for v in e}) == 2 * len(chosen):
            best = max(best, len(chosen))
    return best


def head_scores(oriented_edges):
    edges = list(oriented_edges)
    J = rooted_signed_counts(edges)
    vertices = sorted(J)
    assert sum(J.values()) == 0
    degree = {v: sum(u == v for u, _ in edges) for v in vertices}
    weighted_sum = sum(degree[v] * J[v] for v in vertices)
    K = {v: len(vertices) * degree[v] * J[v] - weighted_sum for v in vertices}
    assert sum(K.values()) == 0
    result = []
    for i, (u, v) in enumerate(edges):
        side = {u}
        changed = True
        while changed:
            changed = False
            for j, (x, y) in enumerate(edges):
                if j == i:
                    continue
                if (x in side) != (y in side):
                    side.update((x, y))
                    changed = True
        sj = sum(J[x] for x in side)
        sk = sum(K[x] for x in side)
        result.append(sj * (K[u] - K[v]) - sk * (J[u] - J[v]))
    assert sum(result) == 0
    return result, J, weighted_sum


def canonical_score(edges, root, apex=0):
    scores, J, weighted_sum = head_scores(list(edges) + [(root, apex)])
    assert J[root] == 0 or J[apex] == 0
    assert scores[-1] == J[apex] * weighted_sum
    return scores[-1]


def normalized_key(edges, root, apex=0):
    vertices = sorted({apex, root} | {v for e in edges for v in e})
    # sigma(x_i-x_j) = x_i-min(x_i,x_j).
    kappa = {v: int(v == root) - int(v == apex) for v in vertices}
    for u, _ in edges:
        kappa[u] += 1
    return tuple(kappa[v] for v in vertices), tuple(sorted(tuple(sorted(e)) for e in edges))


def main():
    start = time.monotonic()
    trees = orientations = essential = 0
    for n in (3, 5):
        for code in product(range(n), repeat=n - 2):
            edges = prufer_tree(code, n)
            assert rooted_signed_counts(edges) == brute_signed_counts(edges)
            maximum = matching_number(edges)
            deficient = [matching_number(edges[:i] + edges[i+1:]) < (n - 1) // 2
                         for i in range(n - 1)]
            for mask in range(1 << (n - 1)):
                oriented = [(v, u) if mask >> i & 1 else (u, v)
                            for i, (u, v) in enumerate(edges)]
                scores, J, _ = head_scores(oriented)
                assert all(not bad or score == 0 for bad, score in zip(deficient, scores))
                if maximum < (n - 1) // 2:
                    assert not any(J.values())
                essential += sum(deficient)
                orientations += 1
            trees += 1
    targets = []
    for n in (3, 5, 7, 9, 11, 13):
        total = 0
        nonzero = 0
        for mask in range(1, 1 << (n - 2)):
            cuts = {j for j in range(1, n - 1) if mask >> (j - 1) & 1}
            edges = [(1 + max([0] + [i for i in cuts if i < j]), j + 1)
                     for j in range(1, n - 1)]
            score = canonical_score(edges, max(cuts) + 1)
            total += (-1) ** (n + len(cuts)) * score
            nonzero += score != 0
        targets.append(dict(arity=n, signed_caterpillar_sum=total,
                            necessary_full_orbit_response=str(Fraction(total, factorial(n))),
                            nonzero_descriptions=nonzero))
    first = [(2, 1), (3, 1), (2, 4)]
    second = [(2, 1), (1, 3), (4, 2)]
    relabel = [0, 2, 1, 4, 3]
    transformed = [(relabel[u], relabel[v]) for u, v in first]
    assert normalized_key(transformed, relabel[1]) == normalized_key(second, 1)
    assert canonical_score(first, 1) == -1 and canonical_score(second, 1) == 0
    result = dict(status='EXACT_HEAD_CURRENT_COMBINATORIAL_CONTROLS_AND_DESCENT_REFUTATION_PASS',
                  labelled_trees=trees, oriented_trees=orientations,
                  deficient_head_checks=essential, targets=targets,
                  seconds=time.monotonic() - start,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  exact_counterexample=dict(first_edges=first, second_edges=second, root=1,
                                            relabel=relabel, first_score=-1, second_score=0),
                  scope='Head exchange and matching vanishing pass. Exact root-slide equality refutes rational-kernel descent. Target responses are only formal necessary values of the refuted score.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
