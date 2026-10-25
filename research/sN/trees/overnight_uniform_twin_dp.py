#!/usr/bin/env python3
"""Independent finite controls for the outward-twin matching-count bound.

All rooted tree shapes through six vertices, all five edge states, and all
root-connected subsets.  Through five vertices also inspect every actual
canonical frozen germ at one declared negative superincreasing base point.
"""
from itertools import product
from pathlib import Path
import hashlib
import json
import time


def children(parent):
    out = [[] for _ in parent]
    for child in range(1, len(parent)):
        out[parent[child]].append(child)
    return out


def rooted_shapes(n):
    seen = {}
    for suffix in product(*(range(i) for i in range(1, n))):
        parent = (-1,) + suffix
        kids = children(parent)
        def code(v):
            return '(' + ''.join(sorted(code(c) for c in kids[v])) + ')'
        seen.setdefault(code(0), parent)
    return list(seen.values())


def matching_counts(kids):
    full = [0] * len(kids)
    deleted = [0] * len(kids)
    for v in reversed(range(len(kids))):
        deleted[v] = prod(full[c] for c in kids[v])
        full[v] = deleted[v] + sum(deleted[c] * prod(full[d] for d in kids[v] if d != c)
                                  for c in kids[v])
    return full


def prod(values):
    out = 1
    for value in values:
        out *= value
    return out


def dynamic_counts(kids, states):
    full = [0] * len(kids)
    singleton = [0] * len(kids)
    for v in reversed(range(len(kids))):
        if any(states[c] in (1, 2) for c in kids[v]):
            continue
        inward = [c for c in kids[v] if states[c] == 4]
        outward = [c for c in kids[v] if states[c] == 3]
        singleton[v] = int(not inward)
        normal = {c: 1 + full[c] - singleton[c] for c in outward}
        full[v] = prod(full[c] for c in inward) * (
            prod(normal.values()) + sum(singleton[c] * prod(normal[d] for d in outward if d != c)
                                       for c in outward))
    return full, singleton


def direct_rooted_subsets(parent, kids, states, root):
    descendants = {root}
    for v in range(root + 1, len(parent)):
        if parent[v] in descendants:
            descendants.add(v)
    result = []
    optional = sorted(descendants - {root})
    for bits in range(1 << len(optional)):
        selected = {root} | {v for j, v in enumerate(optional) if bits >> j & 1}
        if any(parent[v] not in selected for v in selected if v != root):
            continue
        valid = True
        for v in selected:
            selected_singletons = 0
            for c in kids[v]:
                state = states[c]
                if state in (1, 2) or (state == 0 and c in selected) or (state == 4 and c not in selected):
                    valid = False
                    break
                if state == 3 and c in selected and not any(d in selected for d in kids[c]):
                    selected_singletons += 1
            if not valid or selected_singletons > 1:
                valid = False
                break
        if valid:
            result.append(frozenset(selected))
    return result


def actual_eligible(parent, states):
    n = len(parent)
    accepted = []
    for mask in range(1, 1 << n):
        selected = {v for v in range(n) if mask >> v & 1}
        x = [0 if v in selected else -100 ** (v + 1) for v in range(n)] + [0]
        head = [int(v == 0) - int(v == n) for v in range(n + 1)]
        internal = []
        for c in range(1, n):
            p, state = parent[c], states[c]
            if state == 0:
                continue
            positive, negative = (c, p) if state in (1, 3) else (p, c)
            if state in (3, 4) and c in selected and p in selected:
                internal.append((positive, negative))
            elif state in (1, 2) or x[positive] > x[negative]:
                head[positive] += 1
                head[negative] -= 1
        if sum(a * b for a, b in zip(head, x)) != 0:
            continue
        assert all(head[v] == 0 for v in range(n) if v not in selected)
        if len(internal) != len(selected) - 1:
            continue
        effective = [v for v in selected if head[v] == 1]
        assert len(effective) == 1
        root = effective[0]
        assert all(head[v] == int(v == root) for v in selected)
        degrees = {v: sum(v in edge for edge in internal) for v in selected}
        leaf_hubs = [negative for positive, negative in internal
                     if positive != root and degrees[positive] == 1]
        if len(leaf_hubs) != len(set(leaf_hubs)):
            continue
        accepted.append((root, frozenset(selected)))
    return accepted


def fibonacci(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def main():
    start = time.monotonic()
    records = []
    for n in range(1, 7):
        configurations = germs = 0
        shapes = rooted_shapes(n)
        for parent in shapes:
            kids = children(parent)
            matching = matching_counts(kids)
            assert matching[0] <= fibonacci(n + 1)
            for edge_states in product(range(5), repeat=n - 1):
                states = (-1,) + edge_states
                full, singleton = dynamic_counts(kids, states)
                direct = [direct_rooted_subsets(parent, kids, states, v) for v in range(n)]
                assert full == [len(sets) for sets in direct]
                assert singleton == [int(frozenset({v}) in direct[v]) for v in range(n)]
                assert all(full[v] <= matching[v] - (1 - singleton[v]) for v in range(n))
                assert sum(full) <= fibonacci(n + 3) - 2
                if n <= 5:
                    for root, selected in actual_eligible(parent, states):
                        assert selected in direct[root]
                        germs += 1
                configurations += 1
        row = dict(vertices=n, rooted_shapes=len(shapes), configurations=configurations,
                   actual_eligible_germs_checked=germs,
                   exact_subset_recurrence=True, strengthened_matching_bound=True,
                   summed_fibonacci_bound=True)
        records.append(row)
        print(json.dumps(row), flush=True)
    data = dict(status="EXACT_FINITE_OUTWARD_TWIN_COUNT_CONTROLS", rows=records,
                seconds=time.monotonic() - start,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope="Necessary combinatorial capacity only; no uniform outward-twin separator is constructed. Actual germ checks use outside values -100^(v+1), with original root0 and apex n.")
    Path(__file__).with_suffix('.json').write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(data), flush=True)


if __name__ == '__main__':
    main()
