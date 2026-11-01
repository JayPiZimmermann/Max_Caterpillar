#!/usr/bin/env python3
"""Retain both root positions in the exact interval boundary-state ansatz."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, math, random, time
from flint import fmpq_mat
import overnight_upper_interval_polynomial as kernel

HERE = Path(__file__).parent


def canonical(n, key):
    p, r, s, i, j = key
    q = n-p
    orbit = [key, (p, p-1-r, q-1-s, i, j)]
    if p == q:
        orbit += [(p, s, r, q-1-j, p-1-i),
                  (p, q-1-s, p-1-r, q-1-j, p-1-i)]
    return min(orbit)


def descriptors(n):
    return sorted({canonical(n, (p, r, s, i, j))
                   for p in range(1, n//2+1)
                   for r in range(p) for s in range(n-p)
                   for i in range(p) for j in range(n-p)})


def row(omega):
    n = len(omega)
    columns = {key: Q(0) for key in descriptors(n)}
    for p in range(1, n//2+1):
        q = n-p
        for shift in range(n):
            cycle = omega[shift:]+omega[:shift]
            left, right = cycle[:p], cycle[p:]
            a = sum(right)
            prefactor = Q(-a)**(n-4)
            first = [kernel.H(left[r+1:]+left[:r], a) for r in range(p)]
            second = [kernel.H(right[s+1:]+right[:s], a) for s in range(q)]
            for r in range(p):
                for s in range(q):
                    for i in range(p):
                        for j in range(q):
                            columns[canonical(n, (p, r, s, i, j))] += prefactor*first[r][i]*second[s][j]
    kernel.H.cache_clear()
    return list(columns.values())+[Q((-1)**(n-1), math.prod(omega))]


def main():
    start = time.monotonic()
    rng = random.Random(251039)
    records = []
    for n in (4, 5, 6):
        desc = descriptors(n)
        points, rows = [], []
        while len(rows) < len(desc)+8:
            positive = [rng.randrange(1, 10)]
            while len(positive) < n-1:
                positive.append(3*sum(positive)+rng.randrange(1, 10))
            omega = tuple([-sum(positive)]+positive)
            try:
                values = row(omega)
            except ZeroDivisionError:
                kernel.H.cache_clear()
                continue
            denominator = math.lcm(*(v.denominator for v in values))
            rows.append([int(v*denominator) for v in values])
            points.append(omega)
        ordinary = fmpq_mat([r[:-1] for r in rows]).rank()
        augmented = fmpq_mat(rows).rank()
        status = 'EXACT_EVALUATION_DIAGNOSTIC'
        if ordinary == len(desc) and augmented == ordinary+1:
            status = 'EXACT_FULL_COLUMN_ROOT_STATE_OBSTRUCTION'
        record = dict(n=n, descriptors=desc, points=points, integer_rows=rows,
                      ranks=[ordinary, augmented], status=status)
        if ordinary == augmented:
            reduced, rank = fmpq_mat(rows).rref()
            coefficients = ['0']*len(desc)
            for i in range(rank):
                pivot = next(j for j in range(len(desc)) if reduced[i, j])
                coefficients[pivot] = str(reduced[i, len(desc)])
            record['candidate_coefficients'] = coefficients
        records.append(record)
        print('ROOT POSITION RULE', n, 'COLS', len(desc), 'RANKS', record['ranks'],
              status, 'SECONDS', time.monotonic()-start, flush=True)
        if augmented > ordinary:
            break
    result = dict(status='INTERVAL_ROOT_POSITION_COEFFICIENT_TEST', records=records,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  kernel_sha256=hashlib.sha256(Path(kernel.__file__).read_bytes()).hexdigest(),
                  scope='Coefficients may depend on component size, both root positions relative to the interval boundaries, and both positive-away edge counts. Tree shapes and finer orientation placement are summed uniformly. Reflection and equal-size component exchange are exact orbit normalizations.',
                  seconds=time.monotonic()-start)
    (HERE/'overnight_upper_interval_roots.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
