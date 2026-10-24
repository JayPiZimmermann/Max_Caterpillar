#!/usr/bin/env python3
"""Independent complete-flag replay and bounded symbolic certificate review.

Reads root-owned receipts but writes only exponential_families_review_* files.
No uniform sufficiency claim and no Lean verification claim.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).parent
sys.path.insert(0, str(HERE / 'all_tree_dfs'))


def load(mode, n):
    source = HERE / f'exponential_families_{mode}_{n}.json'
    data = json.loads(source.read_text())
    assert data['status'] == 'EXACT_TOP_IDENTITY'
    assert data['n'] == n and data['family'] == mode
    coefficients = list(map(Q, data['coefficient_proposal']))
    assert len(coefficients) == len(data['orbits'])
    return source, data, coefficients


def flags(mode, n):
    from complete_flags import pyramid, simplex, sub
    started = time.monotonic()
    source, data, coefficients = load(mode, n)
    e = [tuple(int(i == j) for i in range(n)) for j in range(n)]
    target = simplex(tuple(e))
    residual = defaultdict(Q, {key: -Q(value) for key, value in target.items()})
    unit_count, orbit_count, first_column = 0, 0, None
    for coefficient, orbit in zip(coefficients, data['orbits']):
        if not coefficient:
            continue
        orbit_count += 1
        for raw_head, raw_edges in orbit:
            head, edges = tuple(raw_head), tuple(map(tuple, raw_edges))
            assert sum(head) == 0 and len(edges) == n - 2
            vertices = set(v for edge in edges for v in edge)
            apex, = set(range(n)) - vertices
            assert head[apex] == -1
            generators = tuple(sorted(sub(e[u], e[v]) for u, v in edges))
            column = pyramid(head, generators)
            if first_column is None:
                first_column = column
            for key, value in column.items():
                residual[key] += coefficient * Q(value)
            unit_count += 1
        if time.monotonic() - started > 110:
            raise TimeoutError('Independent complete-flag review budget; no conclusion')
    bad = {key: value for key, value in residual.items() if value}
    assert not bad, ('complete-flag identity failed', len(bad))
    # A unit perturbation must be seen by the same complete invariant.
    assert first_column and any(first_column.values())
    result = dict(status='INDEPENDENT_COMPLETE_FLAG_IDENTITY_PASS', n=n, family=mode,
                  nonzero_orbits=orbit_count, nonzero_full_units=unit_count,
                  complete_flag_rows=len(residual), residual_nonzero_rows=len(bad),
                  coefficient_perturbation_detected=True,
                  source=source.name, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  elapsed_seconds=time.monotonic() - started)
    (HERE / f'exponential_families_review_flags_{mode}_{n}.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


def symbolic(mode, n):
    from exponential_families_probe import exact_expression
    from rational_identity import Verifier
    started = time.monotonic()
    source, data, coefficients = load(mode, n)
    expression = exact_expression(n, data['orbits'], coefficients)
    verifier = Verifier(budget=100)
    assert verifier.check(expression)
    result = dict(status='SYMBOLIC_IDENTITY_REPLAY_PASS', n=n, family=mode,
                  independent_algorithm=False, nonzero_orbits=sum(bool(c) for c in coefficients),
                  nonzero_full_units=sum(len(o) for c, o in zip(coefficients, data['orbits']) if c),
                  symbolic_calls=verifier.calls, expression_terms=len(expression),
                  source=source.name, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  elapsed_seconds=time.monotonic() - started)
    (HERE / f'exponential_families_review_symbolic_{mode}_{n}.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('method', choices=['flags', 'symbolic'])
    parser.add_argument('family', choices=['bfs', 'deque', 'hierarchy'])
    parser.add_argument('n', type=int)
    args = parser.parse_args()
    (flags if args.method == 'flags' else symbolic)(args.family, args.n)
