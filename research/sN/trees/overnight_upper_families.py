#!/usr/bin/env python3
"""Exact bounded generators for the renewed balanced-hierarchy upper search.

These are family definitions/counts, not spanning claims. Own output names
start overnight_upper_. All orientations and head roots are available.
"""
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import time

from exponential_families import hierarchy, normalize, pruefer
from exponential_families_probe import canonical, permute

HERE = Path(__file__).parent


@lru_cache(None)
def balanced(n):
    if n == 1:
        return ((),)
    out = set()
    for k in range((n + 2) // 3, (2 * n) // 3 + 1):
        for left, right in itertools.product(balanced(k), balanced(n - k)):
            right = tuple((u + k, v + k) for u, v in right)
            for u, v in itertools.product(range(k), range(k, n)):
                out.add(normalize(left + right + ((u, v),)))
    return tuple(sorted(out))


def dihedral_trees(trees, n):
    return {normalize((((sign * u + shift) % n), ((sign * v + shift) % n)) for u, v in tree)
            for tree in trees for sign, shift in itertools.product((-1, 1), range(n))}


def perfect_matching(tree, n):
    if n % 2:
        return False
    edge_set = set(tree)

    def rec(vertices):
        if not vertices:
            return True
        v = min(vertices)
        return any(tuple(sorted((v, w))) in edge_set and rec(vertices - {v, w})
                   for w in vertices if w != v)

    return rec(set(range(n)))


def orbit_family(trees, N):
    base = set()
    for tree in trees:
        for root in range(1, N):
            h = [0] * N
            h[0], h[root] = -1, 1
            for mask in range(1 << (N - 2)):
                edges = [(v + 1, u + 1) if mask >> j & 1 else (u + 1, v + 1)
                         for j, (u, v) in enumerate(tree)]
                base.add(canonical(h, edges))
    orbits = {}
    for key in base:
        orbit = tuple(sorted({permute(key, [(sign * j + shift) % N for j in range(N)])
                              for sign, shift in itertools.product((-1, 1), range(N))}))
        orbits.setdefault(orbit[0], orbit)
    return [orbits[key] for key in sorted(orbits)]


def main():
    started = time.monotonic()
    records = []
    for n in range(2, 8):
        old = dihedral_trees(hierarchy(n), n)
        new = dihedral_trees(balanced(n), n)
        union = old | new
        all_trees = set(pruefer(n))
        assert union <= all_trees
        record = dict(nonapex_vertices=n, old_count=len(old), balanced_count=len(new),
                      union_count=len(union), new_beyond_old=len(new - old),
                      old_beyond_balanced=len(old - new),
                      new_perfect_matching=sum(perfect_matching(t, n) for t in new - old))
        if n == 6:
            groups = [('new_perfect', sorted(t for t in new - old if perfect_matching(t, n))),
                      ('new_deficient', sorted(t for t in new - old if not perfect_matching(t, n))),
                      ('all_balanced', sorted(new))]
            for name, trees in groups:
                orbits = orbit_family(trees, n + 1)
                record[name + '_orbits'] = len(orbits)
                dest = HERE / f'overnight_upper_{name}_{n+1}_family.json'
                data = dict(status='EXACT_FAMILY_ENUMERATION_NO_SPAN_CLAIM', n=n + 1,
                            family=name, tree_count=len(trees), trees=trees, orbit_count=len(orbits), orbits=orbits,
                            generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
                dest.write_text(json.dumps(data, separators=(',', ':')) + '\n')
        records.append(record)
        print(json.dumps(record), flush=True)
    data = dict(status='EXACT_FAMILY_ENUMERATION_NO_SPAN_CLAIM', records=records,
                elapsed_seconds=time.monotonic() - started,
                generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (HERE / 'overnight_upper_balanced_counts.json').write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
