#!/usr/bin/env python3
"""Falsify a one-evaluation separator for OUTWARD twins, not all twins.

Producer: repository research venv Python this.py 5 (or 7).
Budget: 60 seconds per prime arity. No zero sample proves a uniform identity.
A nonzero modular specialization with all denominators invertible refutes
vanishing at the corresponding primitive complex root of unity: reduction
from Z[zeta_m] is a ring homomorphism. This is not a modular rank argument.
"""
import itertools
import json
import math
from pathlib import Path
import sys
import time

import sympy as sp

import dfs_review_fourier as fourier


def outward_twins(unit):
    neighbours = {}
    for u, v in unit["edges"]:
        neighbours.setdefault(u, []).append(v)
        neighbours.setdefault(v, []).append(u)
    by_hub = {}
    for leaf, ns in neighbours.items():
        if leaf != unit["root"] and len(ns) == 1 and (leaf, ns[0]) in unit["edges"]:
            by_hub.setdefault(ns[0], []).append(leaf)
    return [(hub, leaves) for hub, leaves in by_hub.items() if len(leaves) >= 2]


def main(m):
    assert sp.isprime(m) and m >= 5
    start = time.monotonic()
    prime = int(sp.nextprime(10**9))
    while (prime - 1) % m:
        prime = int(sp.nextprime(prime))
    zeta = pow(int(sp.primitive_root(prime)), (prime - 1) // m, prime)
    pt = [pow(zeta, i, prime) for i in range(m)]
    assert sum(pt) % prime == 0 and len(set(pt)) == m
    fourier.P = prime
    perms = list(itertools.permutations(range(m)))
    family = [u for u in fourier.family(m, "twin") if outward_twins(u)]
    tested, zero, witness = 0, 0, None
    for unit in family:
        value = fourier.orbit_mod(unit, pt, m, perms)
        tested += 1
        if value:
            witness = dict(unit=unit, twins=outward_twins(unit), value=value)
            break
        zero += 1
        if time.monotonic() - start > 60:
            break
    data = dict(
        arity=m, prime=prime, zeta=zeta, point=pt,
        family_orbits=len(family), tested=tested, zero=zero, witness=witness,
        target=((-1)**(m-1) * pow(math.prod(pt) % prime, prime-2, prime)) % prime,
        elapsed_seconds=time.monotonic()-start,
        status="ONE_EVALUATION_SEPARATOR_REFUTED" if witness else "NO_COUNTEREXAMPLE_IN_TESTED_ORBITS",
        scope="Only the proposed single roots-of-unity evaluation; outward-twin separation by another functional remains open.",
    )
    dest = Path(__file__).with_name(f"orientation_roots_unity_{m}.json")
    dest.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main(int(sys.argv[1]))
