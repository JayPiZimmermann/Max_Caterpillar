#!/usr/bin/env python3
"""Concrete exponential-size labelled tree families; finite combinatorial checks.

No spanning assertion is made. Count all cyclic relabelings of breadth-first,
deque-traversal, and fixed balanced-hierarchy trees. Verify the small families
against independent Pruefer enumeration. Standard library only, 60 s budget.
"""
from collections import deque
from functools import lru_cache
import hashlib
import itertools
import json
import math
from pathlib import Path
import time


def normalize(edges):
    return tuple(sorted(tuple(sorted(e)) for e in edges))


@lru_cache(None)
def breadth_first(n):
    """Root 0; children of processed vertices receive consecutive new labels."""
    out = []

    def visit(i, assigned, edges):
        if i == n:
            assert assigned == n
            out.append(normalize(edges))
            return
        for degree in range(n - assigned + 1):
            end = assigned + degree
            if i < n - 1 and end <= i + 1:
                continue
            visit(i + 1, end, edges + [(i, j) for j in range(assigned, end)])

    visit(0, 1, [])
    assert len(out) == math.comb(2 * n - 2, n - 1) // n
    return tuple(out)


@lru_cache(None)
def deque_trees(n):
    """A plane tree and n front/back choices; labels follow the visit order."""
    out = set()
    for edges in breadth_first(n):
        children = [[] for _ in range(n)]
        for u, v in edges:
            children[u].append(v)
        # First choice is irrelevant because the root is the sole pending node.
        for mask in range(1 << (n - 1)):
            pending = deque([0])
            order = []
            for step in range(n):
                v = pending.pop() if step and mask >> (step - 1) & 1 else pending.popleft()
                order.append(v)
                pending.extend(children[v])
            pi = {v: i for i, v in enumerate(order)}
            out.add(normalize((pi[u], pi[v]) for u, v in edges))
    return tuple(sorted(out))


@lru_cache(None)
def hierarchy(n):
    """Complete dyadic hierarchy on next-power-of-two leaves, pruned to [n]."""
    def rec(start, width):
        active = list(range(start, min(start + width, n)))
        if len(active) <= 1:
            return [()]
        half = width // 2
        left = list(range(start, min(start + half, n)))
        right = list(range(start + half, min(start + width, n)))
        a = rec(start, half)
        if not right:
            return a
        b = rec(start + half, half)
        return [normalize(x + y + ((u, v),))
                for x, y, u, v in itertools.product(a, b, left, right)]
    return tuple(rec(0, 1 << (n - 1).bit_length()))


def cyclic_closure(family, n):
    return {normalize(((u + shift) % n, (v + shift) % n) for u, v in edges)
            for edges in family for shift in range(n)}


def crosses(e, f):
    a, b = sorted(e)
    c, d = sorted(f)
    return a < c < b < d or c < a < d < b


def two_page(edges):
    """Exactly test bipartiteness of the edge-crossing graph."""
    colours = {}
    for start in range(len(edges)):
        if start in colours:
            continue
        colours[start] = 0
        pending = [start]
        while pending:
            i = pending.pop()
            for j in range(len(edges)):
                if not crosses(edges[i], edges[j]):
                    continue
                if j in colours:
                    if colours[j] == colours[i]:
                        return False
                else:
                    colours[j] = 1 - colours[i]
                    pending.append(j)
    return True


def pruefer(n):
    for code in itertools.product(range(n), repeat=n - 2):
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
        yield normalize(edges)


def main():
    start = time.monotonic()
    records = []
    for n in range(2, 8):
        all_trees = set(pruefer(n))
        record = dict(vertices=n, all_labelled=len(all_trees))
        families = {}
        for name, producer in [('breadth_first', breadth_first), ('deque', deque_trees), ('hierarchy', hierarchy)]:
            base = producer(n)
            family = cyclic_closure(base, n)
            reflected = {normalize((n - 1 - u, n - 1 - v) for u, v in t) for t in family}
            dihedral = family | reflected
            assert family <= all_trees
            assert set().union(*(set(t) for t in family)) == set(itertools.combinations(range(n), 2))
            record[name] = dict(base_count=len(base), cyclic_count=len(family),
                                dihedral_count=len(dihedral),
                                crossing_trees=sum(any(crosses(e, f) for e, f in itertools.combinations(t, 2)) for t in family))
            families[name] = family
        assert families['breadth_first'] <= families['deque']
        record['noncrossing'] = sum(not any(crosses(e, f) for e, f in itertools.combinations(t, 2)) for t in all_trees)
        record['two_page'] = sum(two_page(t) for t in all_trees)
        record['deque_not_two_page'] = len(families['deque'] - {t for t in all_trees if two_page(t)})
        record['two_page_not_deque'] = len({t for t in all_trees if two_page(t)} - families['deque'])
        records.append(record)
        print(json.dumps(record), flush=True)
        if time.monotonic() - start > 60:
            break
    dest = Path(__file__).with_name('exponential_families_counts.json')
    data = dict(status='EXACT_FINITE_COMBINATORIAL_CHECKS_NO_SPAN_CLAIM',
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                budget_seconds=60, seconds=time.monotonic() - start, records=records)
    dest.write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
