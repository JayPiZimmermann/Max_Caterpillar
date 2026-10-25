#!/usr/bin/env python3
"""Exact finite controls for the uniform pseudoforest witness proof."""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import hashlib
import json
import time


def main():
    start = time.monotonic()
    records = []
    for n in range(1, 7):
        possible = list(combinations(range(n), 2))
        tested = selected_sets = cyclic = 0
        for mask in range(1 << len(possible)):
            if mask.bit_count() > n:
                continue
            edges = [e for i, e in enumerate(possible) if mask >> i & 1]
            groups = list(range(n))
            def find(v):
                while groups[v] != v:
                    v = groups[v]
                return v
            for u, v in edges:
                groups[find(u)] = find(v)
            vertex_counts = Counter(find(v) for v in range(n))
            edge_counts = Counter(find(u) for u, v in edges)
            if any(edge_counts[c] > size for c, size in vertex_counts.items()):
                continue
            adjacency = [set() for _ in range(n)]
            for u, v in edges:
                adjacency[u].add(v)
                adjacency[v].add(u)
            core = [set(a) for a in adjacency]
            remaining = set(range(n))
            parent = {}
            while True:
                leaf = next((v for v in sorted(remaining) if len(core[v]) <= 1), None)
                if leaf is None:
                    break
                parent[leaf] = next(iter(core[leaf]), None)
                if parent[leaf] is not None:
                    core[parent[leaf]].remove(leaf)
                remaining.remove(leaf)
            has_cycle = bool(remaining)
            while remaining:
                first = min(remaining)
                previous = None
                v = first
                while True:
                    w = next(w for w in sorted(core[v]) if w != previous)
                    parent[w] = v
                    remaining.remove(v)
                    if w == first:
                        break
                    previous, v = v, w
            assert len(parent) == n
            assert sum(v is not None for v in parent.values()) == len(edges)
            assert all(parent[u] == v or parent[v] == u for u, v in edges)
            matching = []
            for chosen in range(1 << len(edges)):
                candidate = [e for i, e in enumerate(edges) if chosen >> i & 1]
                if len(candidate) > len(matching) and len({v for e in candidate for v in e}) == 2 * len(candidate):
                    matching = candidate
            children = [v if parent[v] == u else u for u, v in matching]
            isolated = [v for v in range(n) if not adjacency[v]]
            nu = len(matching)
            k = nu + len(isolated)
            assert (max(map(len, adjacency)) + 1) * k >= n
            uniform_low = biased_low = 0
            for chosen in range(1 << n):
                selected = {v for v in range(n) if chosen >> v & 1}
                todo = set(selected)
                components = 0
                while todo:
                    components += 1
                    queue = [todo.pop()]
                    for v in queue:
                        fresh = adjacency[v] & todo
                        queue.extend(fresh)
                        todo -= fresh
                witnesses = sum(v in selected and parent[v] not in selected for v in children)
                witnesses += sum(v in selected for v in isolated)
                assert witnesses <= components
                if components <= 2:
                    uniform_low += 1
                    biased_low += 2 ** len(selected) * 11 ** (n - len(selected))
                selected_sets += 1
            uniform_bound = sum(Fraction(comb(k, j) * 3 ** (k-j), 4 ** k)
                                for j in range(min(k, 2) + 1))
            biased_bound = sum(Fraction(comb(nu, j) * 22 ** j * 147 ** (nu-j), 169 ** nu)
                               for j in range(min(nu, 2) + 1))
            assert Fraction(uniform_low, 2 ** n) <= uniform_bound
            assert Fraction(biased_low, 13 ** n) <= biased_bound
            tested += 1
            cyclic += has_cycle
        records.append(dict(vertices=n, pseudoforests=tested, with_cycles=cyclic,
                            selected_sets=selected_sets))
    result = dict(status='EXACT_PSEUDOFOREST_COMPONENT_AND_PROBABILITY_CONTROLS_PASS',
                  records=records, seconds=time.monotonic()-start,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Finite controls; the uniform mathematical proof is in overnight_pseudoforest_matching.md.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
