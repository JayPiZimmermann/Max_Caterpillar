#!/usr/bin/env python3
"""Exact top-class obstruction for FULL bicentre units at N=5.

Seven exact functional identities bound rank by 31. A nonsingular modular
32-by-32 augmented Fourier minor bounds the rational augmented rank below
by 32. This does not exclude the larger all-five-state leaf dictionary.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
import itertools
import json
import math
from pathlib import Path

HERE = Path(__file__).parent
DEST = HERE / 'bicenter_review_top5_certificate.json'


def profile_column(key):
    """Independent, non-NumPy enumeration of all 120 sorted-chamber profiles."""
    h, edges = key
    column = defaultdict(int)
    for pi in itertools.permutations(range(5)):
        a = []
        prefix = set()
        for v in pi[:-1]:
            prefix.add(v)
            a.append(sum(h[w] for w in prefix)
                     + sum(u in prefix and w not in prefix for u, w in edges))
        if min(a) >= 0:
            for j, value in enumerate(a):
                column[('linear', j)] += value
        elif max(a) <= 0:
            continue
        else:
            divisor = math.gcd(*a)
            sign = 1 if next(v for v in a if v) > 0 else -1
            normal = tuple(sign * v // divisor for v in a)
            column[('kink',) + normal] += divisor
            if sign == -1:
                for j, value in enumerate(a):
                    column[('linear', j)] += value
    return dict(column)


def independent_family():
    """Enumerate raw labelled root/orientation choices, then actual automorphisms."""
    def normalized(h, edges):
        h = list(h)
        canonical_edges = []
        for u, v in edges:
            if u > v:
                h[u] += 1
                h[v] -= 1
                u, v = v, u
            canonical_edges.append((u, v))
        return tuple(h), tuple(sorted(canonical_edges))

    def orbit(h, edges):
        choices = []
        for centre_swap, leaf_swap in itertools.product((False, True), repeat=2):
            pi = list(range(5))
            if centre_swap:
                pi[1], pi[2] = 2, 1
            if leaf_swap:
                pi[3], pi[4] = 4, 3
            head = [0] * 5
            for i, v in enumerate(h):
                head[pi[i]] = v
            choices.append(normalized(head, [(pi[u], pi[v]) for u, v in edges]))
        return min(choices)

    family = set()
    potential = [(1, 3), (1, 4), (2, 3), (2, 4)]
    for root, mask, centre_state in itertools.product(range(1, 5), range(16), range(5)):
        h = [0] * 5
        h[0], h[root] = -1, 1
        edges = [(v, u) if mask >> j & 1 else (u, v)
                 for j, (u, v) in enumerate(potential)]
        if centre_state in (1, 2):
            sign = 1 if centre_state == 1 else -1
            h[1] += sign
            h[2] -= sign
        elif centre_state >= 3:
            edges.append((1, 2) if centre_state == 3 else (2, 1))
        family.add(orbit(h, edges))
    return sorted(family)


def determinant_mod(matrix, prime):
    matrix = [list(row) for row in matrix]
    det = 1
    for j in range(len(matrix)):
        pivot = next((i for i in range(j, len(matrix)) if matrix[i][j] % prime), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            det = -det
        value = matrix[j][j] % prime
        det = det * value % prime
        inv = pow(value, -1, prime)
        for i in range(j + 1, len(matrix)):
            scale = matrix[i][j] * inv % prime
            for k in range(j + 1, len(matrix)):
                matrix[i][k] = (matrix[i][k] - scale * matrix[j][k]) % prime
    return det % prime


def produce():
    from flint import fmpq_mat, nmod_mat
    keys = independent_family()
    columns = [profile_column(key) for key in keys]
    rows = sorted(set().union(*(set(c) for c in columns)))
    reduced, rank = fmpq_mat([[c.get(row, 0) for c in columns] for row in rows]).rref()
    pivots = [next(j for j in range(len(keys)) if reduced[i, j]) for i in range(rank)]
    free = [j for j in range(len(keys)) if j not in pivots]
    kernels = []
    for j in free:
        vector = [Q(0)] * len(keys)
        vector[j] = Q(1)
        for i, pivot in enumerate(pivots):
            vector[pivot] = -Q(str(reduced[i, j]))
        kernels.append([str(v) for v in vector])
    probe = json.loads((HERE / 'bicenter_review_top_5.json').read_text())
    original_keys = json.loads((HERE / 'bicenter_probe_5.json').read_text())['keys']
    original_keys = [(tuple(h), tuple(map(tuple, es))) for h, es in original_keys]
    assert original_keys == keys
    matrix = probe['matrix']
    prime = probe['prime']
    mod, mrank = nmod_mat(matrix, prime).rref()
    selected_columns = [next(j for j in range(len(keys) + 1) if mod[i, j]) for i in range(mrank)]
    transposed = [[row[j] for row in matrix] for j in selected_columns]
    modt, trank = nmod_mat(transposed, prime).rref()
    selected_rows = [next(j for j in range(len(matrix)) if modt[i, j]) for i in range(trank)]
    data = dict(n=5, family='full K2,2 leaf hinges, all orientations/roots, all five centre states',
                status='EXACT_TOP_CLASS_OBSTRUCTION', keys=keys, functional_rank_upper=rank,
                independent_kernel_free_columns=free, kernels=kernels,
                prime=prime, minor_columns=selected_columns,
                minor_frequencies=[probe['frequencies'][j] for j in selected_rows],
                claimed_augmented_rank_lower=mrank)
    DEST.write_text(json.dumps(data, indent=2) + '\n')


def check():
    import numpy as np
    from bicenter_review_fourier import full_mod_batch
    data = json.loads(DEST.read_text())
    keys = [(tuple(h), tuple(map(tuple, es))) for h, es in data['keys']]
    assert keys == independent_family()
    assert len(keys) == 38
    columns = [profile_column(key) for key in keys]
    rows = set().union(*(set(c) for c in columns))
    free = data['independent_kernel_free_columns']
    assert len(free) == len(set(free)) == 7
    for i, raw in enumerate(data['kernels']):
        vector = list(map(Q, raw))
        assert len(vector) == 38
        assert [vector[j] for j in free] == [Q(i == j) for j in range(7)]
        for row in rows:
            assert sum(v * c.get(row, 0) for v, c in zip(vector, columns)) == 0
    assert len(data['kernels']) == 7
    prime = data['prime']
    assert prime == 1000003
    assert all(prime % j for j in range(2, math.isqrt(prime) + 1))
    inverse = np.zeros(prime, dtype=np.int64)
    inverse[1] = 1
    for j in range(2, prime):
        inverse[j] = prime - (prime // j) * inverse[prime % j] % prime
    permutations = np.array(list(itertools.permutations(range(5))), dtype=np.int64)
    selected = data['minor_columns']
    assert len(selected) == len(set(selected)) == 32
    assert 38 in selected
    matrix = []
    for om in data['minor_frequencies']:
        assert sum(om) % prime == 0
        permuted = np.array(om, dtype=np.int64)[permutations]
        row = []
        for j in selected:
            if j == 38:
                row.append(pow(math.prod(om) % prime, -1, prime))
            else:
                h, edges = keys[j]
                kappa = list(h)
                for u, v in edges:
                    kappa[u] += 1
                row.append(int(full_mod_batch(kappa, 0, 1, 2, permuted, inverse, prime).sum() % prime))
        matrix.append(row)
    assert len(matrix) == 32
    determinant = determinant_mod(matrix, prime)
    assert determinant
    print(json.dumps(dict(status='EXACT_TOP_CLASS_OBSTRUCTION_VERIFIED', n=5,
                          full_unit_orbits=38, independent_exact_kernel_identities=7,
                          ordinary_rank_upper=31, augmented_rank_lower=32,
                          modular_minor_determinant=determinant, prime=prime), indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('command', choices=['produce', 'check'])
    args = parser.parse_args()
    if args.command == 'produce':
        produce()
    check()
