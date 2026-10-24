#!/usr/bin/env python3
"""Exact symmetric-chamber test for the full bicentre family.

Leaf edges are all hinges, in every orientation. The optional centre edge
has all five states. Canonical heads have any nonapex root. The complete
formal face-state dictionary is larger and is NOT excluded by a negative
result here. Budget 120 seconds per arity; <=5 million matrix entries.
Uses NumPy and python-flint (research/sN/dfs/h5-growth/venv/bin/python).
"""
from collections import defaultdict
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

import numpy as np
from flint import fmpq_mat, nmod_mat

from cycle_fourier import canonical, permute


def compositions(n, k):
    if k == 1:
        yield (n,)
    else:
        for j in range(n + 1):
            for rest in compositions(n - j, k - 1):
                yield (j,) + rest


def orbit_key(key):
    n = len(key[0])
    candidates = []
    for swap in (False, True):
        pi = list(range(n))
        if swap:
            pi[1], pi[2] = 2, 1
        h, es = permute(key, pi)
        leaves = sorted(range(3, n), key=lambda i: h[i])
        pi = list(range(n))
        for new, old in enumerate(leaves, 3):
            pi[old] = new
        candidates.append(permute((h, es), pi))
    return min(candidates)


def family(n):
    out = set()
    for counts in compositions(n - 3, 4):
        types = [t for t, count in enumerate(counts) for _ in range(count)]
        roots = [1, 2] + [3 + types.index(t) for t in range(4) if t in types]
        for root in roots:
            for centre_state in range(5):
                h = [0] * n
                h[0], h[root] = -1, 1
                es = []
                for leaf, typ in enumerate(types, 3):
                    es += [(leaf, c) if typ >> b & 1 else (c, leaf) for b, c in enumerate((1, 2))]
                if centre_state in (1, 2):
                    sign = 1 if centre_state == 1 else -1
                    h[1] += sign
                    h[2] -= sign
                elif centre_state >= 3:
                    es.append((1, 2) if centre_state == 3 else (2, 1))
                out.add(orbit_key(canonical(h, es)))
    return sorted(out)


def chamber_column(key, prefixes, membership):
    h, es = key
    n = len(h)
    values = membership @ np.array(h, dtype=np.int64)
    for u, v in es:
        values += membership[:, u] * (1 - membership[:, v])
    profiles, counts = np.unique(values[prefixes], axis=0, return_counts=True)
    positive = np.all(profiles >= 0, axis=1)
    negative = np.all(profiles <= 0, axis=1)
    linear = (profiles[positive] * counts[positive, None]).sum(axis=0)
    mixed = profiles[~(positive | negative)]
    multiplicity = counts[~(positive | negative)]
    col = {}
    if len(mixed):
        first = mixed[np.arange(len(mixed)), (mixed != 0).argmax(axis=1)]
        flip = first < 0
        linear += (mixed[flip] * multiplicity[flip, None]).sum(axis=0)
        gcds = np.gcd.reduce(np.abs(mixed), axis=1)
        normal = mixed // gcds[:, None]
        normal[flip] *= -1
        for a, weight in zip(normal, gcds * multiplicity):
            row = tuple(map(int, a))
            col[row] = col.get(row, 0) + int(weight)
    for j, value in enumerate(linear):
        if value:
            row = tuple(int(i == j) for i in range(n - 1))
            col[row] = int(value)
    return col


def main(n):
    start = time.monotonic()
    keys = family(n)
    permutations = np.array(list(itertools.permutations(range(n))), dtype=np.int64)
    prefixes = np.bitwise_or.accumulate(1 << permutations, axis=1)[:, :-1]
    membership = np.array([[mask >> i & 1 for i in range(n)] for mask in range(1 << n)], dtype=np.int64)
    print('DOMAIN', n, 'full bicentre orbits', len(keys), 'permutations', len(permutations), flush=True)
    columns = []
    for i, key in enumerate(keys):
        columns.append(chamber_column(key, prefixes, membership))
        if (i + 1) % 50 == 0:
            print('COLUMNS', i + 1, 'SECONDS', round(time.monotonic() - start, 2), flush=True)
        if time.monotonic() - start > 120:
            raise TimeoutError('column generation budget; no mathematical conclusion')
    linear_rows = [tuple(int(i == j) for i in range(n - 1)) for j in range(n - 1)]
    columns.append({row: (j + 1) * (n - j - 1) for j, row in enumerate(linear_rows)})
    target = {row: n - j - 1 for j, row in enumerate(linear_rows)}
    row_keys = sorted(set(target).union(*(set(c) for c in columns)))
    num_cols = len(columns)
    data = dict(n=n, family='full K2,L leaf hinges, every root/orientation, all five centre-edge states',
                orbit_count=len(keys), constraint_rows=len(row_keys), keys=keys, budget_seconds=120,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('MATRIX', len(row_keys), num_cols + 1, flush=True)
    if len(row_keys) * (num_cols + 1) > 5_000_000:
        data['status'] = 'MATRIX_BUDGET_REACHED_NO_CONCLUSION'
    else:
        # Transposed modular elimination proposes a small set of constraint rows.
        transposed = [[c.get(row, 0) for row in row_keys] for c in columns + [target]]
        reduced, rank = nmod_mat(transposed, 1000003).rref()
        selected = [next(j for j in range(len(row_keys)) if reduced[i, j]) for i in range(rank)]
        small = [[c.get(row_keys[j], 0) for c in columns + [target]] for j in selected]
        exact, exact_rank = fmpq_mat(small).rref()
        pivots = [next(j for j in range(num_cols + 1) if exact[i, j]) for i in range(exact_rank)]
        print('EXACT RANK', exact_rank, 'target pivot', num_cols in pivots, flush=True)
        if num_cols in pivots:
            system = [[small[j][i] for j in range(len(small))] + [int(i == num_cols)] for i in range(num_cols + 1)]
            sep, srank = fmpq_mat(system).rref()
            weights = [Fraction(0)] * len(small)
            for i in range(srank):
                pivot = next(j for j in range(len(small) + 1) if sep[i, j])
                assert pivot < len(small)
                weights[pivot] = Fraction(str(sep[i, len(small)]))
            for i in range(num_cols + 1):
                assert sum(weights[j] * small[j][i] for j in range(len(small))) == int(i == num_cols)
            data['status'] = 'EXACT_FULL_UNIT_DICTIONARY_OBSTRUCTION'
            data['separator'] = [dict(row=row_keys[j], weight=str(w)) for j, w in zip(selected, weights) if w]
        else:
            coeff = [Fraction(0)] * num_cols
            for i, pivot in enumerate(pivots):
                coeff[pivot] = Fraction(str(exact[i, num_cols]))
            bad = []
            for row in row_keys:
                if sum(co * c.get(row, 0) for co, c in zip(coeff, columns)) != target.get(row, 0):
                    bad.append(row)
            data['status'] = 'EXACT_SYMMETRIC_IDENTITY' if not bad else 'CANDIDATE_FAILED_FULL_CONSTRAINT_CHECK'
            data['bad_rows'] = len(bad)
            data['coefficients'] = [str(c) for c in coeff]
        data['modular_augmented_rank'] = rank
        data['exact_selected_rank'] = exact_rank
    data['elapsed_seconds'] = time.monotonic() - start
    dest = Path(__file__).with_name(f'bicenter_probe_{n}.json')
    dest.write_text(json.dumps(data, indent=2) + '\n')
    print('DONE', data['status'], 'SECONDS', data['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]))
