#!/usr/bin/env python3
"""Checkpointed modular proposals and exact gates for balanced hierarchy N=7.

Dense samples are disk-backed. FLINT matrices are filled row-by-row to avoid
the multi-gigabyte Python-int-list constructor. Each invocation is bounded
by overnight_upper_run.py. No sampled positive is promoted without the exact
rational-identity gate.
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
from flint import nmod_mat, ctx

from exponential_families_batch import engine, evaluate, PRIME
from exponential_families_probe import exact_expression, ratrec
from rational_identity import Verifier, add
from gluing_review_gates import dfs_value_mod

HERE = Path(__file__).parent
ctx.threads = 1
SEED = 24102561


def stem(mode):
    return HERE / f'overnight_upper_{mode}_7'


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(8 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def source_orbits(mode):
    old_source = HERE / 'exponential_batch_hierarchy_full_7.json'
    old = json.loads(old_source.read_text())
    gate = json.loads((HERE / 'exponential_kernel_hierarchy_full_7.json').read_text())
    assert gate['status'] == 'ALL_EXACT_KERNEL_IDENTITIES_VERIFIED'
    assert gate['source_sha256'] == digest(old_source)
    removed = set(old['kernel_free_columns'])
    assert len(removed) == 296
    orbits = [orbit for i, orbit in enumerate(old['orbits']) if i not in removed]
    sources = [dict(path=old_source.name, sha256=digest(old_source), retained=len(orbits),
                    exact_kernel_source='exponential_kernel_hierarchy_full_7.json')]
    names = ['new_perfect'] if mode == 'perfect' else ['new_perfect', 'new_deficient']
    for name in names:
        path = HERE / f'overnight_upper_{name}_7_family.json'
        data = json.loads(path.read_text())
        orbits.extend(data['orbits'])
        sources.append(dict(path=path.name, sha256=digest(path), retained=len(data['orbits'])))
    return orbits, sources


def generate(mode):
    started = time.monotonic()
    path = stem(mode)
    metadata = path.with_suffix('.json')
    matrix_path = path.with_suffix('.u32')
    orbits, sources = source_orbits(mode)
    width, rows = len(orbits), len(orbits) + 32
    print('FAMILY', mode, width, 'ROWS', rows, flush=True)
    keys, offsets, forms, incidence, apices = engine(7, orbits)
    print('ENGINE', len(keys), 'UNITS', len(forms), 'FACTORS', flush=True)
    if metadata.exists():
        data = json.loads(metadata.read_text())
        assert data['sources'] == sources
        points, completed = data['points'], data['completed_rows']
    else:
        rng = random.Random(SEED)
        points, rejected = [], 0
        while len(points) < rows:
            point = [rng.randrange(1, 1000000) for _ in range(6)]
            point.append(-sum(point))
            rng.shuffle(point)
            if np.all(np.array(point, dtype=np.int64) @ forms.T % PRIME) and math.prod(point) % PRIME:
                points.append(point)
            else:
                rejected += 1
        completed = 0
        data = dict(status='MATRIX_GENERATION_PENDING', n=7, family=mode,
                    orbit_columns=width, rows=rows, prime=PRIME, seed=SEED,
                    sources=sources, points=points, rejected_points=rejected,
                    completed_rows=0, producer_sha256=digest(Path(__file__)))
        metadata.write_text(json.dumps(data, separators=(',', ':')) + '\n')
    first, unused = evaluate(7, points[:1], offsets, forms, incidence, apices)
    independent = [sum(dfs_value_mod((tuple(h), tuple(map(tuple, es))), points[0], PRIME)
                       for h, es in orbit) % PRIME for orbit in orbits]
    independent.append(pow(math.prod(points[0]) % PRIME, -1, PRIME))
    assert independent == list(map(int, first[0]))
    data['independent_first_row_entries'] = width + 1
    print('INDEPENDENT FIRST ROW PASS', width + 1, flush=True)
    matrix = np.memmap(matrix_path, dtype=np.uint32, mode='r+' if matrix_path.exists() else 'w+', shape=(rows, width + 1))
    for start in range(completed, rows, 16):
        block = points[start:start + 16]
        values, unused = evaluate(7, block, offsets, forms, incidence, apices)
        matrix[start:start + len(block)] = values
        completed = start + len(block)
        if completed % 320 == 0 or completed == rows:
            matrix.flush()
            data['completed_rows'] = completed
            metadata.write_text(json.dumps(data, separators=(',', ':')) + '\n')
            print('ROWS', completed, 'SECONDS', round(time.monotonic() - started, 1), flush=True)
        if time.monotonic() - started > 1100:
            break
    matrix.flush()
    del matrix
    data['completed_rows'] = completed
    if completed == rows:
        data.update(status='MATRIX_COMPLETE', matrix_sha256=digest(matrix_path))
    data['generation_seconds_this_run'] = time.monotonic() - started
    metadata.write_text(json.dumps(data, separators=(',', ':')) + '\n')
    print('DONE', data['status'], completed, flush=True)


def solve(mode):
    started = time.monotonic()
    path = stem(mode)
    metadata = path.with_suffix('.json')
    data = json.loads(metadata.read_text())
    assert data['completed_rows'] == data['rows']
    width, rows = data['orbit_columns'], data['rows']
    matrix_path = path.with_suffix('.u32')
    assert digest(matrix_path) == data['matrix_sha256']
    print('ALLOCATE', rows, width + 1, 'FLINT BYTES', rows * (width + 1) * 8, flush=True)
    matrix = nmod_mat(rows, width + 1, PRIME)
    with matrix_path.open('rb') as f:
        for i in range(rows):
            row = np.fromfile(f, dtype=np.uint32, count=width + 1)
            assert len(row) == width + 1
            for j, value in enumerate(row):
                matrix[i, j] = int(value)
            if i % 1000 == 0:
                print('FILL', i, 'SECONDS', round(time.monotonic() - started, 1), flush=True)
    print('RREF', 'SECONDS', round(time.monotonic() - started, 1), flush=True)
    reduced, rank = matrix.rref(inplace=True)
    pivots = [next(j for j in range(width + 1) if reduced[i, j]) for i in range(rank)]
    target_pivot = width in pivots
    data.update(status='MODULAR_DIAGNOSTIC_ONLY', ranks=[rank - int(target_pivot), rank])
    print('RANKS', data['ranks'], 'SECONDS', round(time.monotonic() - started, 1), flush=True)
    if not target_pivot:
        coefficients = [Q(0)] * width
        for i, pivot in enumerate(pivots):
            coefficients[pivot] = ratrec(int(reduced[i, width]), PRIME)
        data['rational_reconstructed'] = sum(c is not None for c in coefficients)
        if all(c is not None for c in coefficients):
            data['coefficient_proposal'] = [str(c) for c in coefficients]
            data['status'] = 'RATIONAL_PROPOSAL_PENDING_EXACT_GATE'
            print('PROPOSAL SUPPORT', sum(bool(c) for c in coefficients), flush=True)
    else:
        free = [j for j in range(width) if j not in pivots]
        proposals = []
        for j in free:
            vector = [[j, '1']]
            for i, pivot in enumerate(pivots):
                if pivot == width:
                    continue
                value = -int(reduced[i, j]) % PRIME
                if value:
                    coefficient = ratrec(value, PRIME)
                    if coefficient is None:
                        vector = None
                        break
                    vector.append([pivot, str(coefficient)])
            proposals.append(vector)
        data.update(kernel_free_columns=free, kernel_proposals=proposals)
        print('KERNEL PROPOSALS', sum(v is not None for v in proposals), '/', len(proposals), flush=True)
    data['solve_seconds'] = time.monotonic() - started
    metadata.write_text(json.dumps(data, separators=(',', ':')) + '\n')


def verify(mode):
    path = stem(mode).with_suffix('.json')
    data = json.loads(path.read_text())
    orbits, sources = source_orbits(mode)
    assert sources == data['sources']
    coefficients = list(map(Q, data['coefficient_proposal']))
    expression = exact_expression(7, orbits, coefficients)
    print('EXACT EXPRESSION', len(expression), 'TERMS', flush=True)
    verifier = Verifier(budget=1100)
    try:
        ok = verifier.check(expression)
        data['status'] = 'EXACT_TOP_IDENTITY' if ok else 'RATIONAL_PROPOSAL_FAILED'
    except TimeoutError:
        data['status'] = 'EXACT_GATE_BUDGET_REACHED_NO_CONCLUSION'
    data.update(symbolic_calls=verifier.calls, symbolic_seconds=time.time() - verifier.start)
    path.write_text(json.dumps(data, separators=(',', ':')) + '\n')
    print('DONE', data['status'], data['symbolic_calls'], flush=True)


def kernels(mode):
    """Verify rational nullspace proposals independently of sampled rank."""
    path = stem(mode).with_suffix('.json')
    data = json.loads(path.read_text())
    orbits, sources = source_orbits(mode)
    assert sources == data['sources']
    free, proposals = data['kernel_free_columns'], data['kernel_proposals']
    assert len(free) == len(proposals) == len(set(free)) and all(v is not None for v in proposals)
    for f, raw in zip(free, proposals):
        vector = {j: Q(c) for j, c in raw}
        assert len(vector) == len(raw)
        assert [vector.get(j, Q(0)) for j in free] == [Q(j == f) for j in free]
    passed = data.get('exact_kernel_passed', [])
    verifier = Verifier(budget=1100)
    forms = [tuple(int(i == j) for i in range(6)) + (0,) for j in range(6)] + [(-1,) * 6 + (0,)]
    one = (0,) * 6 + (1,)
    for index, raw in enumerate(proposals):
        if index in passed:
            continue
        expression = exact_expression(7, [orbits[j] for j, c in raw], [Q(c) for j, c in raw])
        add(expression, 1, one, 0, [(f, 1) for f in forms])
        try:
            assert verifier.check(expression), ('kernel proposal failed', index)
        except TimeoutError:
            break
        passed.append(index)
        if len(passed) % 10 == 0:
            data['exact_kernel_passed'] = passed
            path.write_text(json.dumps(data, separators=(',', ':')) + '\n')
            print('KERNELS', len(passed), '/', len(proposals), 'SECONDS', round(time.time() - verifier.start, 1), flush=True)
    data['exact_kernel_passed'] = passed
    data['exact_kernel_calls_this_run'] = verifier.calls
    if len(passed) == len(proposals):
        data['ordinary_rank_upper'] = len(orbits) - len(proposals)
        assert data['ordinary_rank_upper'] < data['ranks'][1]
        data['status'] = 'EXACT_SUBFAMILY_TOP_OBSTRUCTION' if mode == 'perfect' else 'EXACT_BALANCED_HIERARCHY_TOP_OBSTRUCTION'
    path.write_text(json.dumps(data, separators=(',', ':')) + '\n')
    print('DONE', data['status'], len(passed), '/', len(proposals), flush=True)


if __name__ == '__main__':
    mode, command = sys.argv[1:]
    assert mode in ('perfect', 'balanced')
    {'generate': generate, 'solve': solve, 'verify': verify, 'kernels': kernels}[command](mode)
