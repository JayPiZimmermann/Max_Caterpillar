#!/usr/bin/env python3
"""Bounded dihedral top-class probes for the exponential traversal families.

All roots and orientations, cyclic changes of the nonapex traversal order,
and global dihedral closure. Missing/linear tree edges vanish in this quotient.
Modular ranks propose identities; the symbolic principal-parts checker is the
positive gate. Uses the h5-growth venv (NumPy and python-flint).
"""
from collections import defaultdict
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

HERE = Path(__file__).parent
sys.path.insert(0, str(HERE.parent / 'cycles'))
sys.path.insert(0, str(HERE / 'all_tree_dfs'))
from cycle_fourier import canonical, cuts, permute
from exponential_families import breadth_first, deque_trees, hierarchy, cyclic_closure
from rational_identity import add, Verifier

PRIME = 1000003
SEED = 24102431


def ratrec(value, prime):
    r0, r1, t0, t1 = prime, int(value), 0, 1
    limit = math.isqrt(prime // 2)
    while abs(r1) > limit:
        q = r0 // r1
        r0, r1, t0, t1 = r1, r0 - q * r1, t1, t0 - q * t1
    if not t1 or abs(t1) > limit:
        return None
    answer = Q(r1, t1)
    return answer if (answer.numerator - value * answer.denominator) % prime == 0 else None


def family(n, mode):
    producer = {'bfs': breadth_first, 'deque': deque_trees, 'hierarchy': hierarchy}[mode]
    trees = cyclic_closure(producer(n - 1), n - 1)
    base = set()
    for tree in trees:
        for root in range(1, n):
            h = [0] * n
            h[0], h[root] = -1, 1
            for mask in range(1 << (n - 2)):
                es = [(v + 1, u + 1) if mask >> j & 1 else (u + 1, v + 1)
                      for j, (u, v) in enumerate(tree)]
                base.add(canonical(h, es))
    orbits = {}
    for key in base:
        orbit = tuple(sorted({permute(key, [(sign * j + shift) % n for j in range(n)])
                              for sign in (-1, 1) for shift in range(n)}))
        orbits.setdefault(orbit[0], orbit)
    return len(trees), [orbits[key] for key in sorted(orbits)]


def exact_expression(n, orbits, coefficients):
    forms = [tuple(int(i == j) for i in range(n - 1)) + (0,) for j in range(n - 1)]
    forms.append((-1,) * (n - 1) + (0,))
    one = (0,) * (n - 1) + (1,)
    expr = defaultdict(Q)
    for coeff, orbit in zip(coefficients, orbits):
        if not coeff:
            continue
        for key in orbit:
            vertices = {v for edge in key[1] for v in edge}
            apex, = set(range(n)) - vertices
            aa = forms[apex]
            den = []
            for side, head in cuts(key, apex):
                q = tuple(sum(forms[i][j] for i in side) for j in range(n))
                den += [(tuple(x + head * a for x, a in zip(q, aa)), 1),
                        (tuple(x + (head + 1) * a for x, a in zip(q, aa)), 1)]
            add(expr, coeff, tuple(-x for x in aa), n - 4, den)
    add(expr, -((-1) ** (n - 1)), one, 0, [(f, 1) for f in forms])
    return expr


def main(n, mode):
    started = time.monotonic()
    tree_count, orbits = family(n, mode)
    width = len(orbits)
    data = dict(n=n, family=mode, cyclic_tree_count=tree_count, orbits=orbits,
                orbit_count=width, prime=PRIME, seed=SEED, budget_seconds=120,
                symbolic_budget_seconds=40, matrix_entry_budget=8_000_000,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    dest = HERE / f'exponential_families_{mode}_{n}.json'
    print('DOMAIN', n, mode, 'trees', tree_count, 'orbits', width,
          'generation', round(time.monotonic() - started, 2), flush=True)
    row_count = min(width + 24, 2500)
    if (width + 1) * row_count > 8_000_000 or time.monotonic() - started > 120:
        data.update(status='BUDGET_REACHED_NO_CONCLUSION', seconds=time.monotonic() - started)
        dest.write_text(json.dumps(data) + '\n')
        print(data['status'], flush=True)
        return
    keys = [key for orb in orbits for key in orb]
    offsets = np.cumsum([0] + [len(orb) for orb in orbits])[:-1]
    apex = [next(i for i in range(n) if not any(i in e for e in key[1])) for key in keys]
    all_cuts = [cuts(key, a) for key, a in zip(keys, apex)]
    masks = np.array([[sum(1 << v for v in side) for side, head in cc] for cc in all_cuts], dtype=np.int64)
    heads = np.array([[head for side, head in cc] for cc in all_cuts], dtype=np.int64)
    membership = np.array([[mask >> i & 1 for i in range(n)] for mask in range(1 << n)], dtype=np.int64)
    apex = np.array(apex, dtype=np.int64)
    inverse = np.zeros(PRIME, dtype=np.int64)
    inverse[1] = 1
    for j in range(2, PRIME):
        inverse[j] = PRIME - (PRIME // j) * inverse[PRIME % j] % PRIME
    rng = random.Random(SEED)
    rows, points = [], []
    rejected = 0
    for _ in range(row_count):
        while True:
            pt = [rng.randrange(1, 100000) for _ in range(n - 1)]
            pt.append(-sum(pt))
            rng.shuffle(pt)
            om = np.array(pt, dtype=np.int64) % PRIME
            aa = om[apex]
            qs = (membership @ om)[masks] % PRIME
            den = np.ones(len(keys), dtype=np.int64)
            for j in range(n - 2):
                den = den * ((qs[:, j] + aa * heads[:, j]) % PRIME) % PRIME
                den = den * ((qs[:, j] + aa * (heads[:, j] + 1)) % PRIME) % PRIME
            if np.all(den) and math.prod(pt) % PRIME:
                break
            rejected += 1
        numer = np.ones(len(keys), dtype=np.int64)
        for _ in range(n - 4):
            numer = numer * (-aa) % PRIME
        values = numer * inverse[den] % PRIME
        row = np.add.reduceat(values, offsets) % PRIME
        target = (-1) ** (n - 1) * int(inverse[math.prod(pt) % PRIME]) % PRIME
        rows.append(list(map(int, row)) + [target])
        points.append(pt)
        if time.monotonic() - started > 120:
            break
    reduced, rank = nmod_mat(rows, PRIME).rref()
    pivots = [next(j for j in range(width + 1) if reduced[i, j]) for i in range(rank)]
    data.update(points=points, rows=rows, rejected_pole_points=rejected,
                ranks=[rank - int(width in pivots), rank], status='MODULAR_DIAGNOSTIC_ONLY')
    if rank == width + 1:
        # All rational entries have nonzero denominators modulo PRIME. A full
        # augmented-column minor is a characteristic-zero obstruction.
        data['status'] = 'FULL_COLUMN_MODULAR_RANK_IMPLIES_EXACT_TOP_OBSTRUCTION'
    elif width not in pivots and len(rows) > rank:
        proposed = [Q(0)] * width
        for i, pivot in enumerate(pivots):
            proposed[pivot] = ratrec(int(reduced[i, width]), PRIME)
        if all(x is not None for x in proposed):
            data['coefficient_proposal'] = [str(x) for x in proposed]
            verifier = Verifier(budget=40)
            try:
                result = verifier.check(exact_expression(n, orbits, proposed))
                data['status'] = 'EXACT_TOP_IDENTITY' if result else 'RATIONAL_RECONSTRUCTION_FAILED'
            except TimeoutError:
                data['status'] = 'SYMBOLIC_BUDGET_REACHED_NO_CONCLUSION'
            data['symbolic_calls'] = verifier.calls
    data['seconds'] = time.monotonic() - started
    if data['status'] == 'EXACT_TOP_IDENTITY':
        # The certificate is the exact orbit/coefficient identity. Sampled
        # matrices are deterministic proposals and need not occupy tens of MB.
        sampled = data.pop('rows')
        data['sampled_matrix_rows'] = len(sampled)
        data['sampled_matrix_sha256'] = hashlib.sha256(
            json.dumps(sampled, separators=(',', ':')).encode()).hexdigest()
        data['sampled_matrix_storage'] = 'omitted after exact gate; regenerate with recorded seed and family'
    dest.write_text(json.dumps(data) + '\n')
    print('DONE', data['status'], 'ranks', data['ranks'], 'seconds', round(data['seconds'], 2), flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), sys.argv[2])
