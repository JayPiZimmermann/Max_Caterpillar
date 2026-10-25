#!/usr/bin/env python3
"""Exact top-degree controls for the normalized symmetric graph complex.

No producer or matrix library is imported.  The uniform proof is in the
companion Markdown note; these finite checks audit signs and completeness.
"""
from collections import deque
from functools import lru_cache
from pathlib import Path
import hashlib
import json


@lru_cache(None)
def matchings(vertices):
    if not vertices:
        return ((),)
    first = vertices[0]
    out = []
    for partner in vertices[1:]:
        rest = tuple(v for v in vertices if v not in (first, partner))
        for remaining in matchings(rest):
            out.append(tuple(sorted(((first, partner),) + remaining)))
    return tuple(out)


def pfaffian_sign(matching):
    crossings = sum(a < c < b < d or c < a < d < b
                    for i, (a, b) in enumerate(matching)
                    for c, d in matching[i + 1:])
    return (-1) ** crossings


def wedge_sign(matching):
    flattened = [v for edge in matching for v in edge]
    return (-1) ** sum(flattened[i] > flattened[j]
                       for i in range(len(flattened))
                       for j in range(i + 1, len(flattened)))


def swap_adjacent(matching, i):
    def swap(v):
        return i + 1 if v == i else i if v == i + 1 else v
    return tuple(sorted(tuple(sorted((swap(a), swap(b))))
                        for a, b in matching))


def merge_adjacent(matching, i):
    def merge(v):
        return v if v <= i else v - 1
    graph = tuple(sorted(tuple(sorted((merge(a), merge(b))))
                         for a, b in matching))
    assert len(graph) == len(set(graph))
    assert all(a != b for a, b in graph)
    return graph


def split_cherry(graph, i):
    """Direct graph differential at its unique degree-two vertex."""
    incident = [edge for edge in graph if i in edge]
    assert len(incident) == 2
    outputs = []
    for first_twin in (0, 1):
        assignment = {incident[0]: first_twin, incident[1]: 1 - first_twin}
        edges = []
        for edge in graph:
            result = []
            for v in edge:
                result.append(i + assignment[edge] if v == i
                              else v + int(v > i))
            edges.append(tuple(sorted(result)))
        outputs.append(tuple(sorted(edges)))
    return {matching: (-1) ** (i + 1) for matching in outputs}


def check(k):
    count = 2 * k
    all_matchings = matchings(tuple(range(count)))
    all_set = set(all_matchings)
    adjacency = {matching: set() for matching in all_matchings}
    source_graphs = set()
    for matching in all_matchings:
        assert pfaffian_sign(matching) == wedge_sign(matching)
        for i in range(count - 1):
            if (i, i + 1) in matching:
                continue
            other = swap_adjacent(matching, i)
            assert other in all_set and other != matching
            assert pfaffian_sign(other) == -pfaffian_sign(matching)
            graph = merge_adjacent(matching, i)
            degree = [sum(v in edge for edge in graph)
                      for v in range(count - 1)]
            assert degree.count(2) == 1 and degree.count(1) == count - 2
            assert degree[i] == 2
            boundary = split_cherry(graph, i)
            assert set(boundary) == {matching, other}
            assert sum(coefficient * pfaffian_sign(term)
                       for term, coefficient in boundary.items()) == 0
            source_graphs.add(graph)
            adjacency[matching].add(other)

    standard = tuple((i, i + 1) for i in range(0, count, 2))
    reached = {standard}
    queue = deque([standard])
    while queue:
        for other in adjacency[queue.popleft()]:
            if other not in reached:
                reached.add(other)
                queue.append(other)
    assert reached == all_set
    expected_sources = 0 if k == 1 else (count - 1) * ((count - 2) * (count - 3) // 2) * len(matchings(tuple(range(count - 4))))
    assert len(source_graphs) == expected_sources
    return dict(k=k, top_basis=len(all_matchings),
                source_basis=len(source_graphs),
                adjacent_swap_graph_connected=True,
                every_source_has_two_equal_sign_outputs=True,
                pfaffian_annihilates_every_source=True,
                top_cokernel_rank=1)


def main():
    rows = [check(k) for k in range(1, 6)]
    data = dict(status="EXACT_FINITE_GRAPH_COMPLEX_CONTROLS",
                rows=rows,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope="Graph algebra only. No map from CPWL functions, support functions, or opposite-face flags is asserted.")
    destination = Path(__file__).with_suffix('.json')
    destination.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
