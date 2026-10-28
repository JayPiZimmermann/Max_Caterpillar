#!/usr/bin/env python3
"""Exact coverage inventory before probing binary-linear family closures.

The input is the complete breadth-first family, all cyclic starts and both
traversal directions, with all canonical roots/orientations available. This
file first tests only underlying trees. If its group closure covers all trees,
a positive spanning test at that arity would not discriminate the candidate.
"""
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import sys
import time

from exponential_families import breadth_first, normalize, pruefer
from overnight_upper_families import dihedral_trees

HERE = Path(__file__).parent


def binary_linear_group(affine):
    """GL(3,2) on seven nonzero vectors or AGL(3,2) on eight vectors."""
    maps = []
    for a, b, c in product(range(1, 8), repeat=3):
        values = tuple((a if x & 1 else 0) ^ (b if x & 2 else 0) ^
                       (c if x & 4 else 0) for x in range(8))
        if len(set(values)) != 8:
            continue
        for shift in range(8) if affine else (0,):
            maps.append(tuple(values[x] ^ shift for x in range(8)) if affine
                        else tuple(values[x] - 1 for x in range(1, 8)))
    assert len(set(maps)) == len(maps) == (1344 if affine else 168)
    n = 8 if affine else 7
    assert all(sorted(p) == list(range(n)) for p in maps)
    # Check closure using a generating set of translations, swaps and shears.
    group = set(maps)
    generators = maps[:8] + [maps[len(maps)//3], maps[-1]]
    assert all(tuple(p[q[i]] for i in range(n)) in group
               for p in maps for q in generators)
    return maps


def action(key, permutation):
    apex, edges = key
    return permutation[apex], normalize((permutation[u], permutation[v]) for u, v in edges)


def modular_affine_group(n):
    return [tuple((a*i+b) % n for i in range(n))
            for a in range(n) if math.gcd(a,n) == 1 for b in range(n)]


def inventory(n, modular=False):
    started = time.monotonic()
    group = modular_affine_group(n) if modular else binary_linear_group(n == 8)
    trees = dihedral_trees(breadth_first(n - 1), n - 1)
    base = set()
    for tree in trees:
        key = (0, tuple((u + 1, v + 1) for u, v in tree))
        for shift in range(n):
            base.add(action(key, [(i + shift) % n for i in range(n)]))
    covered, missing, seen = [], [], set()
    for tree in pruefer(n - 1):
        initial = (0, tuple((u + 1, v + 1) for u, v in tree))
        for apex in range(n):
            key = action(initial, [(i + apex) % n for i in range(n)])
            if key in seen:
                continue
            orbit = {action(key, pi) for pi in group}
            seen.update(orbit)
            record = dict(representative=min(orbit), orbit_size=len(orbit),
                          base_members=len(orbit & base))
            (covered if record['base_members'] else missing).append(record)
    assert len(seen) == n * (n - 1) ** (n - 3)
    assert base <= seen
    data = dict(status='EXACT_GRAPH_COVERAGE_NO_SPAN_CLAIM', arity=n,
                group=f'Aff(Z/{n}Z)' if modular else ('AGL(3,2)' if n == 8 else 'GL(3,2)'), group_order=len(group),
                breadth_first_trees_per_apex=len(trees), base_graphs=len(base),
                all_graphs=len(seen), graph_orbits=len(covered)+len(missing),
                covered_orbits=len(covered), missing_orbits=len(missing),
                covered_graphs=sum(x['orbit_size'] for x in covered),
                missing_graphs=sum(x['orbit_size'] for x in missing),
                covered=covered, missing=missing,
                group_permutations=group,
                elapsed_seconds=time.monotonic()-started,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    path = HERE / f'overnight_upper_{"modular" if modular else "linear"}_group_inventory_{n}.json'
    path.write_text(json.dumps(data, separators=(',', ':'))+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ('covered','missing','group_permutations')}), flush=True)


if __name__ == '__main__':
    inventory(int(sys.argv[1]), len(sys.argv)>2 and sys.argv[2]=='modular')
