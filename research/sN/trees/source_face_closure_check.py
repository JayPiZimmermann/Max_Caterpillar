#!/usr/bin/env python3
"""Independent exact source-face controls; receipts are never overwritten."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib
import json
import math
import time

HERE = Path(__file__).parent


def orient(vertices, edges, root):
    adjacency = {v: [] for v in vertices}
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    answer = []
    queue = [root]
    parent = {root: None}
    for v in queue:
        for w in adjacency[v]:
            if w == parent[v]:
                continue
            parent[w] = v
            queue.append(w)
            answer.append((v, w))
    return answer


def passed(adjacency, kappa, tied, outside_order):
    seen = set()
    components = 0
    for v in tied:
        if v in seen:
            continue
        components += 1
        stack = [v]
        seen.add(v)
        while stack:
            u = stack.pop()
            for w in adjacency[u] & tied:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
    if components > 2:
        return False
    if any(kappa[v] == 0 and not (adjacency[v] & tied) for v in tied):
        return False
    higher = set(tied)
    for v in outside_order:
        if len(adjacency[v] & higher) != kappa[v]:
            return False
        higher.add(v)
    return True


def check():
    started = time.monotonic()
    cases = passing_ties = 0
    counts = []
    for n in range(2, 5):
        count = 0
        for word in product(range(n), repeat=n - 2):
            degree = [1] * n
            for v in word:
                degree[v] += 1
            edges = []
            for v in word:
                leaf = next(i for i, d in enumerate(degree) if d == 1)
                edges.append((leaf, v))
                degree[leaf] -= 1
                degree[v] -= 1
            edges.append(tuple(i for i, d in enumerate(degree) if d == 1))
            for source, root in product(range(n), repeat=2):
                oriented = orient(range(n), edges, source)
                for states in product(range(3), repeat=n - 1):
                    head = [int(v == root) for v in range(n)]
                    kept = []
                    for (u, v), state in zip(oriented, states):
                        if state == 2:
                            kept.append((u, v))
                        elif state == 1:
                            head[u] += 1
                            head[v] -= 1
                    adjacency = [set() for _ in range(n + 1)]
                    for u, v in kept:
                        adjacency[u].add(v)
                        adjacency[v].add(u)
                    kappa = [
                        head[v] + sum(u == v for u, _ in kept)
                        for v in range(n)
                    ] + [-1]
                    charge = [kappa[v] - len(adjacency[v]) + 1 for v in range(n)]
                    expected = [int(v == source) + int(v == root) for v in range(n)]
                    for (u, v), state in zip(oriented, states):
                        if state != 2:
                            expected[u if state == 1 else v] += 1
                    assert charge == expected and min(charge) >= 0

                    components = []
                    seen = set()
                    for v in range(n):
                        if v in seen:
                            continue
                        component = {v}
                        seen.add(v)
                        queue = [v]
                        for u in queue:
                            for w in adjacency[u]:
                                if w not in seen:
                                    seen.add(w)
                                    component.add(w)
                                    queue.append(w)
                        assert sum(charge[u] for u in component) == 1 + sum(
                            head[u] for u in component
                        )
                        components.append(component)
                    active = [
                        component for component in components
                        if sum(head[v] for v in component) == 1
                    ]
                    valid = len(active) == 1 and all(
                        component == active[0] or sum(head[v] for v in component) == 0
                        for component in components
                    )
                    component = active[0] if valid else set()
                    smaller = component | {n}
                    if valid:
                        marks = [v for v in sorted(component) for _ in range(charge[v])]
                        assert len(marks) == 2
                        new_edges = orient(
                            component, [edge for edge in kept if edge[0] in component],
                            marks[0]
                        )
                        new_kappa = {
                            v: int(v == marks[1]) + sum(u == v for u, _ in new_edges)
                            for v in component
                        }
                        assert all(new_kappa[v] == kappa[v] for v in component)

                    generating_value = Q(0)
                    for m in range(3, n + 2):
                        for values in combinations(range(n + 1), m):
                            tied = set(values)
                            outside = set(range(n + 1)) - tied
                            good = 0
                            for order in permutations(sorted(outside)):
                                if not passed(adjacency, kappa, tied, order):
                                    continue
                                good += 1
                                passing_ties += 1
                                assert valid and len(component) >= 2 and tied <= smaller
                                restricted = [v for v in order if v in smaller]
                                assert passed(adjacency, kappa, tied, restricted)
                            if good:
                                smaller_good = sum(
                                    passed(adjacency, kappa, tied, order)
                                    for order in permutations(sorted(smaller - tied))
                                )
                                fraction = Q(good, math.factorial(len(outside)))
                                assert fraction <= Q(
                                    smaller_good, math.factorial(len(smaller - tied))
                                )
                                generating_value += fraction * Q(1, 2) ** m
                    assert generating_value ** 2 <= Q(7, 4) ** (n + 1)
                    cases += 1
                    count += 1
        counts.append(dict(tree_vertices=n,faces_source_root_cases=count))
    assert cases == 7167 and passing_ties == 3899
    return dict(
        status="INDEPENDENT_SOURCE_FACE_CHARGE_AND_CAPACITY_CONTROLS_PASS",
        cases=cases, cases_by_size=counts, passing_ordered_ties=passing_ties,
        states={"0": "omit", "1": "linear", "2": "retained"},
        checks=[
            "direct charge update and nonnegativity",
            "component charge versus head sum",
            "fixed unique active component",
            "exact smaller normalized head",
            "every passing order restricts to a smaller passing order",
            "exact fractions have no interleaving loss",
            "original-N generating bound at y=1/2",
        ],
        seconds=time.monotonic() - started,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope="Exhaustive finite convention controls through four nonapex vertices; the independent review note gives the uniform proof. No Lean claim.",
    )


def main():
    parser = ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "source_face_closure_check.json")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(
            f"Refusing to overwrite receipt {args.output}; use --output with a fresh path."
        )
    result = check()
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
