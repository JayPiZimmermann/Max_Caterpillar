#!/usr/bin/env python3
"""Seven-input continuation with batched Fourier factors and exact final gate.

Budgets: 40 million matrix entries, 300 s row generation, 180 s symbolic
verification. A modular rank gap is diagnostic unless augmented columns are
independent. Frequency points, family, rational proposals and hashes are saved;
the sampled matrix is reproducible and kept only in memory. Prime 1000000007,
seed 24102441. The existing producer is unchanged so its receipts stay valid.
"""
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import random
import sys
import time

import numpy as np
from flint import nmod_mat

from exponential_families_probe import family, exact_expression, ratrec
from cycle_fourier import cuts, tree_value
from rational_identity import Verifier

HERE = Path(__file__).parent
PRIME = 1000000007
SEED = 24102441


def array_power(values, exponent):
    out = np.ones_like(values)
    values = values.copy()
    while exponent:
        if exponent & 1:
            out = out * values % PRIME
        exponent >>= 1
        if exponent:
            values = values * values % PRIME
    return out


def source_root(key):
    head, edges = key
    vertices = {v for edge in edges for v in edge}
    marks = [head[v] + 1 - sum(b == v for a, b in edges) for v in vertices]
    return min(marks) >= 0 and sum(marks) == 2


def engine(n, orbits):
    keys = [key for orbit in orbits for key in orbit]
    offsets = np.cumsum([0] + [len(orb) for orb in orbits])[:-1]
    forms, lookup, incidence, apices = [], {}, [], []
    for key in keys:
        vertices = {v for edge in key[1] for v in edge}
        apex, = set(range(n)) - vertices
        apices.append(apex)
        row = []
        for side, head in cuts(key, apex):
            for shift in (head, head + 1):
                form = tuple(int(i in side) + shift * int(i == apex) for i in range(n))
                if form not in lookup:
                    lookup[form] = len(forms)
                    forms.append(form)
                row.append(lookup[form])
        incidence.append(row)
    return keys, offsets, np.array(forms, dtype=np.int64), np.array(incidence, dtype=np.int64), np.array(apices)


def evaluate(n, points, offsets, forms, incidence, apices):
    frequencies = np.array(points, dtype=np.int64) % PRIME
    factors = frequencies @ forms.T % PRIME
    assert np.all(factors), 'pole point must be rejected before evaluation'
    inverse = array_power(factors, PRIME - 2)
    values = array_power((-frequencies[:, apices]) % PRIME, n - 4)
    for j in range(incidence.shape[1]):
        values = values * inverse[:, incidence[:, j]] % PRIME
    rows = np.add.reduceat(values, offsets, axis=1) % PRIME
    targets = np.array([(-1) ** (n - 1) * pow(math.prod(p) % PRIME, -1, PRIME) % PRIME for p in points])
    return np.column_stack((rows, targets)), values


def main(n, mode, restriction):
    started = time.monotonic()
    trees, orbits = family(n, mode)
    if restriction == 'source':
        orbits = [orb for orb in orbits if source_root(orb[0])]
    width = len(orbits)
    count = width + 32
    dest = HERE / f'exponential_batch_{mode}_{restriction}_{n}.json'
    data = dict(n=n, family=mode, orientation_restriction=restriction,
                cyclic_tree_count=trees, orbit_count=width, orbits=orbits,
                prime=PRIME, seed=SEED, matrix_entry_budget=40_000_000,
                row_budget_seconds=300, symbolic_budget_seconds=180,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('DOMAIN', n, mode, restriction, 'orbits', width, 'rows', count, flush=True)
    if (width + 1) * count > 40_000_000:
        data.update(status='MATRIX_BUDGET_REACHED_NO_CONCLUSION', seconds=time.monotonic() - started)
        dest.write_text(json.dumps(data) + '\n')
        print(data['status'], flush=True)
        return
    keys, offsets, forms, incidence, apices = engine(n, orbits)
    print('ENGINE', len(keys), 'units', len(forms), 'distinct factors', flush=True)
    rng = random.Random(SEED)
    points, rejected = [], 0
    while len(points) < count:
        point = [rng.randrange(1, 1000000) for _ in range(n - 1)]
        point.append(-sum(point))
        rng.shuffle(point)
        values = np.array(point, dtype=np.int64) @ forms.T % PRIME
        if np.all(values) and math.prod(point) % PRIME:
            points.append(point)
        else:
            rejected += 1
    first, first_values = evaluate(n, points[:2], offsets, forms, incidence, apices)
    for point_index in range(2):
        for j in sorted({0, len(keys) // 3, len(keys) // 2, len(keys) - 1}):
            exact = tree_value(keys[j], int(apices[j]), points[point_index])
            reduced = exact.numerator % PRIME * pow(exact.denominator % PRIME, -1, PRIME) % PRIME
            assert reduced == first_values[point_index, j]
    data['exact_fraction_scalar_controls'] = 8
    matrix = np.empty((count, width + 1), dtype=np.uint32)
    completed = 0
    for start in range(0, count, 32):
        block = points[start:start + 32]
        rows, unused_values = evaluate(n, block, offsets, forms, incidence, apices)
        matrix[start:start + len(block)] = rows
        completed = start + len(block)
        if start % 320 == 0:
            print('ROWS', completed, 'SECONDS', round(time.monotonic() - started, 2), flush=True)
        if time.monotonic() - started > 300:
            break
    matrix = matrix[:completed]
    data.update(points=points[:completed], matrix_rows=completed, rejected_pole_points=rejected,
                matrix_uint32_sha256=hashlib.sha256(matrix.tobytes()).hexdigest())
    if completed < count:
        data.update(status='ROW_BUDGET_REACHED_NO_CONCLUSION', seconds=time.monotonic() - started)
        dest.write_text(json.dumps(data) + '\n')
        print(data['status'], flush=True)
        return
    print('RREF', matrix.shape, 'SECONDS', round(time.monotonic() - started, 2), flush=True)
    reduced, rank = nmod_mat(matrix.tolist(), PRIME).rref(inplace=True)
    pivots = [next(j for j in range(width + 1) if reduced[i, j]) for i in range(rank)]
    data.update(ranks=[rank - int(width in pivots), rank], status='MODULAR_DIAGNOSTIC_ONLY')
    print('RANKS', data['ranks'], 'SECONDS', round(time.monotonic() - started, 2), flush=True)
    if rank == width + 1:
        data['status'] = 'FULL_COLUMN_MODULAR_RANK_IMPLIES_EXACT_TOP_OBSTRUCTION'
    elif width not in pivots:
        proposed = [Q(0)] * width
        for i, pivot in enumerate(pivots):
            proposed[pivot] = ratrec(int(reduced[i, width]), PRIME)
        data['rational_reconstructed'] = sum(x is not None for x in proposed)
        if all(x is not None for x in proposed):
            data['coefficient_proposal'] = [str(x) for x in proposed]
            data['status'] = 'RATIONAL_PROPOSAL_PENDING_EXACT_GATE'
            dest.write_text(json.dumps(data) + '\n')
            expression = exact_expression(n, orbits, proposed)
            print('SYMBOLIC', len(expression), 'terms', flush=True)
            verifier = Verifier(budget=180)
            try:
                ok = verifier.check(expression)
                data['status'] = 'EXACT_TOP_IDENTITY' if ok else 'RATIONAL_RECONSTRUCTION_FAILED'
            except TimeoutError:
                data['status'] = 'SYMBOLIC_BUDGET_REACHED_NO_CONCLUSION'
            data['symbolic_calls'] = verifier.calls
    data['seconds'] = time.monotonic() - started
    dest.write_text(json.dumps(data) + '\n')
    print('DONE', data['status'], 'SECONDS', round(data['seconds'], 2), flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 'full')
