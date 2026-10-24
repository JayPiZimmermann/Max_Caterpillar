#!/usr/bin/env python3
"""Exact controls for odd-tie counting and the deletion recursion obstruction.

Budget 120 s. No floating point linear algebra. All unoriented trees through
11 vertices for matching counts; all root/orientation/duplicated-leaf choices
on every odd-size tree with 3,5,7 vertices for exposed-vertex identities.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path
import time

import networkx as nx

HERE = Path(__file__).resolve().parent


def matching_masks(edges):
    masks = []
    for chosen in range(1 << len(edges)):
        vertices = 0
        for j, (u, v) in enumerate(edges):
            if not chosen >> j & 1:
                continue
            pair = (1 << u) | (1 << v)
            if vertices & pair:
                break
            vertices |= pair
        else:
            masks.append(vertices)
    return masks


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def generator(size, a, b):
    return tuple(int(j == a)-int(j == b) for j in range(size))


def zonotope(head, gens):
    pts = {head}
    for g in gens:
        pts |= {add(p, g) for p in pts}
    return pts


def main():
    start = time.monotonic()
    fib = [0, 1]
    for j in range(15):
        fib.append(sum(fib[-2:]))
    tree_count = matching_count = duplicate_graphs = vertex_checks = 0
    per_arity = []
    for n in range(2, 12):
        before = vertex_checks
        for G0 in nx.nonisomorphic_trees(n):
            assert time.monotonic()-start < 120
            G = nx.convert_node_labels_to_integers(G0, first_label=1)
            edges = tuple(sorted(tuple(sorted(e)) for e in G.edges()))
            masks = matching_masks(edges)
            assert len(masks) == len(set(masks)), "two forest matchings cover the same set"
            assert len(masks) <= fib[n+1]
            matching_count += len(masks)
            tree_count += 1
            if n not in (3, 5, 7):
                continue
            m = n+1  # Old arity, including apex 0.
            new = m
            leaves = [v for v in G if G.degree(v) == 1]
            for leaf in leaves:
                hub = next(iter(G[leaf]))
                extended_edges = edges + ((hub, new),)
                new_masks = matching_masks(extended_edges)
                assert all(mask.bit_count() < n+1 for mask in new_masks)
                duplicate_graphs += 1
                for root in G:
                    for bits in itertools.product((0, 1), repeat=n-1):
                        oriented = [(u, v) if b else (v, u) for (u, v), b in zip(edges, bits)]
                        head = generator(m+1, root, 0)
                        old_gens = [generator(m+1, u, v) for u, v in oriented]
                        new_gen = generator(m+1, new, hub)
                        old_base = zonotope(head, old_gens)
                        new_base = zonotope(head, old_gens + [new_gen])
                        new_pyramid = new_base | {(0,)*(m+1)}
                        lo = min(p[new] for p in new_pyramid)
                        hi = max(p[new] for p in new_pyramid)
                        assert (lo, hi) == (0, 1)
                        minface = {p[:-1] for p in new_pyramid if p[new] == lo}
                        maxface = {p[:-1] for p in new_pyramid if p[new] == hi}
                        old_pyramid = {p[:-1] for p in old_base} | {(0,)*m}
                        translated_base = {add(p, new_gen)[:-1] for p in old_base}
                        assert minface == old_pyramid
                        assert maxface == translated_base
                        vertex_checks += 1
                        assert time.monotonic()-start < 120
        per_arity.append({"tree_vertices": n, "vertex_checks": vertex_checks-before})
        print("checked n", n, "total trees", tree_count, "vertex identities", vertex_checks,
              "seconds", round(time.monotonic()-start, 3), flush=True)
    for N in range(1, 101):
        assert sum(math.comb(N,j) for j in range(1,N+1,2)) == 1 << (N-1)
    report = {
        "status": "EXACT_FINITE_CONTROLS_PASS_UNIFORM_ARGUMENT_IN_NOTE",
        "tree_count": tree_count,
        "matching_count": matching_count,
        "duplicated_leaf_graphs": duplicate_graphs,
        "vertex_identities": vertex_checks,
        "per_arity": per_arity,
        "budget_seconds": 120,
        "elapsed_seconds": time.monotonic()-start,
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "meaning": "Checks counting and the fixed-coordinate recursion obstruction; does not prove or refute uniform separation",
    }
    (HERE/'reopen_lower_odd_check.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
