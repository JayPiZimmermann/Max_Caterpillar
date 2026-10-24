#!/usr/bin/env python3
"""Exact finite controls for the matching-number arbitrary-orientation bound.

Budget: 90 seconds. Every unlabeled tree on 2..11 vertices, all vertex
subsets; maximum matching independently computed by exhaustive edge subsets.
All inequalities are integer comparisons; no floating-point evidence.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path
import time

import networkx as nx

HERE = Path(__file__).resolve().parent


def adjacency(n, edges):
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return adj


def connected(adj, mask):
    seen = mask & -mask
    todo = seen
    while todo:
        bit = todo & -todo
        todo -= bit
        fresh = adj[bit.bit_length() - 1] & mask & ~seen
        seen |= fresh
        todo |= fresh
    return seen == mask


def exhaustive_matching(n, edges):
    best = ()
    for mask in range(1 << len(edges)):
        if mask.bit_count() <= len(best):
            continue
        used = 0
        chosen = []
        for e, (u, v) in enumerate(edges):
            if not (mask >> e) & 1:
                continue
            bits = (1 << u) | (1 << v)
            if used & bits:
                break
            used |= bits
            chosen.append((u, v))
        else:
            best = tuple(chosen)
    return best


def parents(adj, root):
    parent = {root: root}
    todo = [root]
    while todo:
        u = todo.pop()
        bits = adj[u]
        while bits:
            bit = bits & -bits
            bits -= bit
            v = bit.bit_length() - 1
            if v not in parent:
                parent[v] = u
                todo.append(v)
    return parent


def main():
    start = time.monotonic()
    rows = []
    trees = subsets = rooted_controls = 0
    for n in range(2, 12):
        ntrees = 0
        for G in nx.nonisomorphic_trees(n):
            assert time.monotonic() - start < 90, "90-second budget exhausted"
            edges = tuple(sorted(tuple(sorted(e)) for e in G.edges()))
            adj = adjacency(n, edges)
            match = exhaustive_matching(n, edges)
            nu = len(match)
            # Graph library is only a second matching control, not the producer.
            assert nu == len(nx.max_weight_matching(G, maxcardinality=True))
            roots = [parents(adj, v) for v in range(n)]
            count = weighted = weighted_improved = 0
            leaves = sum(len(G[v]) == 1 for v in G)
            assert 2 * nu >= n - leaves + 1
            root_count = [0] * n
            root_weight = [0] * n
            root_weight_improved = [0] * n
            for mask in range(1, 1 << n):
                subsets += 1
                if not connected(adj, mask):
                    continue
                count += 1
                w = 6 ** (n - mask.bit_count())
                weighted += w
                wi = 2 ** mask.bit_count() * 11 ** (n - mask.bit_count())
                weighted_improved += wi
                for v in range(n):
                    if not (mask >> v) & 1:
                        continue
                    parent = roots[v]
                    for u in range(n):
                        assert not (mask >> u) & 1 or (mask >> parent[u]) & 1
                    for a, b in match:
                        p, c = (a, b) if parent[b] == a else (b, a)
                        assert not ((mask >> c) & 1 and not (mask >> p) & 1)
                    root_count[v] += 1
                    root_weight[v] += w
                    root_weight_improved[v] += wi
                    rooted_controls += 1
            ub = 2 ** (n - 2 * nu) * 3 ** nu
            wb = 7 ** (n - 2 * nu) * 43 ** nu
            wi_bound = 13 ** (n - 2 * nu) * 147 ** nu
            assert count <= n * ub
            assert weighted <= n * wb
            assert weighted_improved <= n * wi_bound
            assert max(root_count) <= ub
            assert max(root_weight) <= wb
            assert max(root_weight_improved) <= wi_bound
            ntrees += 1
            trees += 1
        rows.append({"n": n, "trees": ntrees})
        print("checked", n, ntrees, "trees", round(time.monotonic() - start, 3), flush=True)
    finite_constants = 0
    for N in range(3, 501):
        assert (1 << N) - 1 - N - math.comb(N, 2) >= 1 << (N - 3)
        # 504*(P+N-2+(N-1)/7) = 7N^2+653N-576.
        assert 7*N*N + 653*N - 576 <= 504*(N+1)**2
        assert 26*N*N + 2075*N - 1815 <= 1573*(N+1)**2
        for k in range((N-1)//2 + 1):
            assert N - 2*k >= 1
            # E=(7/6)^(N-2k)*(43/36)^k >= 1 factor by factor.
            finite_constants += 1
    report = {
        "status": "EXACT_FINITE_CONTROLS_PASS_NOT_A_LEAN_PROOF",
        "domain": "all nonisomorphic trees, 2 <= n <= 11; all nonempty vertex subsets",
        "trees": trees,
        "vertex_subsets": subsets,
        "rooted_controls": rooted_controls,
        "finite_constant_instances": finite_constants,
        "weighted_parameters": ["1/6", "2/11"],
        "leaf_count_bound": "2*nu >= n-L+1",
        "per_arity": rows,
        "budget_seconds": 90,
        "elapsed_seconds": time.monotonic() - start,
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (HERE / "orientation_audit_matching.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
