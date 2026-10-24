#!/usr/bin/env python3
"""Budgeted test: must a top-class maximum use a maximally matchable tree?

All canonical heads and edge orientations; retain every hinge. Other face
states vanish in the top quotient. Use all graph automorphism orbits and
full coordinate-permutation sums. Modular ranks are diagnostics only.
Budget 90 seconds, at most 240 frequency rows, prime 1000003.
"""
import itertools
import json
import math
from pathlib import Path
import sys
import time

import networkx as nx
import numpy as np

from dfs_review_fourier import family, points


def main(m, max_matching):
    start = time.monotonic()
    prime = 1000003
    units = []
    for u in family(m, "all"):
        graph = nx.Graph(u["edges"])
        if len(nx.max_weight_matching(graph, maxcardinality=True)) <= max_matching:
            units.append(u)
    perms = np.array(list(itertools.permutations(range(m))), dtype=np.int64)
    cuts = [[(sum(1 << i for i in side), sign) for side, sign in u["cuts"]] for u in units]
    needed = sorted({mask for es in cuts for mask, sign in es})
    inv = np.zeros(prime, dtype=np.int64)
    inv[1] = 1
    for j in range(2, prime):
        inv[j] = prime - (prime // j) * inv[prime % j] % prime
    bases = [{}, {}]
    rows, accepted = [], []

    def insert(row, basis):
        v = np.array(row, dtype=np.int64) % prime
        for j, b in sorted(basis.items()):
            v = (v - v[j] * b) % prime
        nz = np.flatnonzero(v)
        if len(nz):
            j = int(nz[0])
            basis[j] = v * inv[v[j]] % prime

    print("DOMAIN", m, "matching<=", max_matching, "orbits", len(units), flush=True)
    for pt in points(m, 1000):
        om = np.array(pt, dtype=np.int64)[perms] % prime
        apex = om[:, 0]
        qtab = {mask: om[:, [i for i in range(m) if mask >> i & 1]].sum(axis=1) % prime for mask in needed}
        numerator = np.ones(len(perms), dtype=np.int64)
        for _ in range(m - 4):
            numerator = numerator * (-apex) % prime
        row = []
        for es in cuts:
            denominator = np.ones(len(perms), dtype=np.int64)
            for mask, sign in es:
                q = qtab[mask]
                denominator = denominator * q % prime
                denominator = denominator * ((q + sign * apex) % prime) % prime
            if np.any(denominator == 0):
                break
            row.append(int((numerator * inv[denominator] % prime).sum() % prime))
        if len(row) != len(units):
            continue
        target = int(((-1) ** (m - 1) * inv[math.prod(pt) % prime]) % prime)
        insert(row, bases[0])
        insert(row + [target], bases[1])
        rows.append(row + [target])
        accepted.append(pt)
        if len(rows) % 10 == 0:
            print("ROWS", len(rows), "RANKS", *map(len, bases), "SECONDS", round(time.monotonic() - start, 2), flush=True)
        if len(rows) >= 240 or time.monotonic() - start >= 90:
            break
    data = dict(arity=m, max_matching=max_matching, prime=prime, orbits=len(units), rows=len(rows),
                modular_ranks=list(map(len, bases)), points=accepted, evaluations=rows,
                representatives=units, elapsed_seconds=time.monotonic() - start,
                status="MODULAR_DIAGNOSTIC_ONLY", budget_seconds=90)
    dest = Path(__file__).with_name(f"orientation_matching_probe_{m}_{max_matching}.json")
    dest.write_text(json.dumps(data, indent=2) + "\n")
    print("DONE", {k: v for k, v in data.items() if k not in {"points", "evaluations", "representatives"}}, flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
