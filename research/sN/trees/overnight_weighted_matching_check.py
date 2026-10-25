#!/usr/bin/env python3
"""Exact exhaustive controls of the forest component-witness lemma through N=6."""
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import hashlib
import json
import time


def binomial_tail(k):
    return sum(Fraction(comb(k, j) * 3 ** (k - j), 4 ** k)
               for j in range(min(k, 2) + 1))


def main():
    started = time.monotonic()
    records = []
    for n in range(1, 7):
        possible = list(combinations(range(n), 2))
        forests = ties = 0
        for mask in range(1 << len(possible)):
            if mask.bit_count() >= n:
                continue
            edges = [e for i, e in enumerate(possible) if mask >> i & 1]
            groups = list(range(n))
            def find(v):
                while groups[v] != v:
                    v = groups[v]
                return v
            for u, v in edges:
                u, v = find(u), find(v)
                if u == v:
                    break
                groups[u] = v
            else:
                adjacency = [set() for _ in range(n)]
                for u, v in edges:
                    adjacency[u].add(v)
                    adjacency[v].add(u)
                parent = {}
                for root in range(n):
                    if root in parent:
                        continue
                    parent[root] = None
                    queue = [root]
                    for v in queue:
                        for w in adjacency[v]:
                            if w not in parent:
                                parent[w] = v
                                queue.append(w)
                maximum = []
                for choice in range(1 << len(edges)):
                    selected = [e for i, e in enumerate(edges) if choice >> i & 1]
                    if len(selected) > len(maximum) and len({v for e in selected for v in e}) == 2 * len(selected):
                        maximum = selected
                children = [v if parent[v] == u else u for u, v in maximum]
                isolated = [v for v in range(n) if not adjacency[v]]
                degree = max(map(len, adjacency))
                witness_count = len(maximum) + len(isolated)
                assert (degree + 1) * witness_count >= n
                low = 0
                for chosen in range(1 << n):
                    inside = lambda v: chosen >> v & 1
                    components = chosen.bit_count() - sum(inside(u) and inside(v) for u, v in edges)
                    witness = sum(inside(v) and not inside(parent[v]) for v in children)
                    witness += sum(inside(v) for v in isolated)
                    assert witness <= components
                    low += components <= 2
                    ties += 1
                assert Fraction(low, 2 ** n) <= binomial_tail(witness_count)
                assert Fraction(low, 2 ** n) <= binomial_tail(len(maximum))
                forests += 1
        records.append(dict(vertices=n, labelled_forests=forests, selected_sets=ties))
    result = dict(status='EXACT_EXHAUSTIVE_FOREST_WITNESS_CONTROLS_PASS', records=records,
                  seconds=time.monotonic() - started,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Finite implementation controls only; the uniform proof is in overnight_weighted_matching.md.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
