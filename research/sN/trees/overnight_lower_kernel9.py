#!/usr/bin/env python3
"""Propose sparse rational kernel relations from the N9 modular diagnostic.

These are proposals only. Rational-function identity checks are required
before any rank upper bound or separator follows.
"""
import collections
from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys
import time

import numpy as np
from flint import ctx, nmod_mat

HERE = Path(__file__).resolve().parent
P = 1000003


def reconstruct(a, modulus=P):
    """Unique rational reconstruction inside the symmetric sqrt(modulus/2) box."""
    bound = math.isqrt(modulus // 2)
    r0, r1, t0, t1 = modulus, a, 0, 1
    while abs(r1) > bound:
        q = r0 // r1
        r0, r1, t0, t1 = r1, r0-q*r1, t1, t0-q*t1
    if t1 and abs(t1) <= bound and math.gcd(r1, t1) == 1:
        value = Fraction(r1, t1)
        if (value.numerator-a*value.denominator) % modulus == 0:
            return value
    return None


def main():
    started = time.monotonic()
    ctx.threads = 1
    source = HERE/'overnight_lower_matching_matrix_9.u32'
    data = np.fromfile(source, dtype='<u4').reshape(-1, 3823)
    crt = len(sys.argv)>1 and sys.argv[1]=='crt'
    second = None
    if crt:
        selected = json.loads((HERE/'overnight_lower_matching_rank_9.json').read_text())['selected_row_indices']
        data = data[selected, :]
        second_data = np.fromfile(HERE/'overnight_lower_matching_prime2_9.u32', dtype='<u4').reshape(-1, 3823)
        assert second_data.shape == data.shape
        second, second_rank = nmod_mat(second_data.tolist(), 1000033).rref()
        del second_data
        assert second_rank == 1971
    reduced, rank = nmod_mat(data.tolist(), P).rref()
    del data
    pivots = []
    for i in range(rank):
        for j in range(pivots[-1]+1 if pivots else 0, 3823):
            if reduced[i, j]:
                pivots.append(j)
                break
    assert rank == 1971 and pivots[-1] == 3822
    if crt:
        assert all(second[i, j] == int(i==k) for i in range(rank)
                   for k, j in enumerate(pivots))
    print('RREF', rank, 'seconds', time.monotonic()-started, flush=True)
    ordinary = pivots[:-1]
    free = sorted(set(range(3822))-set(ordinary))
    support_counts = collections.Counter()
    failures = []
    coefficient_counts = collections.Counter()
    stem = 'overnight_lower_kernel9_crt' if crt else 'overnight_lower_kernel9_proposals'
    path = HERE/(stem+'.jsonl.gz')
    max_height = 1
    prime_inverse = pow(P, -1, 1000033)
    with gzip.open(path, 'wt') as output:
        for j in free:
            coefficients = [[j, 1, 1]]
            failed = False
            for i, pivot in enumerate(ordinary):
                a = -int(reduced[i, j]) % P
                modulus = P
                if crt:
                    b = -int(second[i, j]) % 1000033
                    a += P*((b-a)*prime_inverse % 1000033)
                    modulus *= 1000033
                if a:
                    value = reconstruct(a, modulus)
                    if value is None:
                        failed = True
                        break
                    coefficients.append([pivot, value.numerator, value.denominator])
                    max_height = max(max_height, abs(value.numerator), value.denominator)
            if failed:
                failures.append(j)
                continue
            support_counts[len(coefficients)] += 1
            coefficient_counts.update((n, d) for _, n, d in coefficients)
            output.write(json.dumps(dict(free_column=j, coefficients=coefficients))+'\n')
    result = dict(status='RATIONAL_KERNEL_PROPOSALS_ONLY', primes=[P,1000033] if crt else [P],
                  modular_rank=rank-1, columns=3822, proposed_relations=len(free)-len(failures),
                  failed_reconstruction_columns=failures,
                  support_count_histogram=dict(sorted(support_counts.items())),
                  common_coefficients=[[n, d, count] for (n, d), count in coefficient_counts.most_common(30)],
                  max_coefficient_height=max_height,
                  matrix_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  proposals_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  seconds=time.monotonic()-started,
                  next_gate='Independent exact rational-function identities for every proposed relation')
    (HERE/(stem+'.json')).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
