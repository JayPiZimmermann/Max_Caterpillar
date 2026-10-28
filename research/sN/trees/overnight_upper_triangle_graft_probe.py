#!/usr/bin/env python3
"""Bounded N7 two-page graft probe with supporting-hyperplane orbit rows."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, random, time
from flint import nmod_mat
import overnight_upper_triangle_attachments as attachment
import overnight_upper_triangle_fixed as fixed
import overnight_upper_product_family as base

HERE = Path(__file__).parent
PRIME = 1000000007
MAX_ENTRIES = 8_000_000


def main():
    start = time.monotonic()
    source = HERE/'overnight_upper_triangle_grafts_7_inventory.json'
    inventory = json.loads(source.read_text())
    descriptors = inventory['descriptors']
    base.raw_chain = attachment.raw_chain
    base.group = fixed.group
    columns = []
    for i, descriptor in enumerate(descriptors):
        columns.append(base.expression(base.sym_chain(7, descriptor)))
        if (i+1) % 100 == 0:
            print('GRAFT COLUMNS', i+1, '/', len(descriptors),
                  'CACHED CUBES', base.cube_kernel.cache_info().currsize,
                  'SECONDS', time.monotonic()-start, flush=True)
    wanted = base.target(7)
    planes = sorted(set(wanted) | {p for c in columns for p in c})
    representatives = {}
    for plane in planes:
        representatives.setdefault(fixed.plane_orbit(plane), plane)
    entries = []
    for orbit, plane in sorted(representatives.items()):
        active = sum(bool(c.get(plane)) for c in columns)
        target = bool(wanted.get(plane))
        quota = min(active+4, 64 if target else 32)
        entries.append(dict(orbit=orbit, plane=plane, active_columns=active,
                            target=target, points=quota))
    width = len(columns)
    cap = min(3200, MAX_ENTRIES//(width+1))
    assert 3*len(entries) <= cap, 'too many hyperplane orbits for the declared entry budget'
    while sum(e['points'] for e in entries) > cap:
        candidate = max((e for e in entries if e['points'] > 3),
                        key=lambda e: (e['points'], not e['target']))
        candidate['points'] -= 1
    print('ROW PLAN', len(planes), 'PLANES', len(entries), 'ORBIT REPS',
          sum(e['points'] for e in entries), 'ROWS', 'SECONDS', time.monotonic()-start, flush=True)
    rng = random.Random(251035)
    rows, points = [], []
    for index, entry in enumerate(entries):
        plane = entry['plane']
        accepted = 0
        while accepted < entry['points']:
            point = tuple(rng.randrange(1, 2000) for _ in range(5))
            try:
                row = [base.evaluate(c.get(plane, {}), point, PRIME) for c in columns]
                row.append(base.evaluate(wanted.get(plane, {}), point, PRIME))
            except ZeroDivisionError:
                continue
            rows.append(row)
            points.append((plane, point))
            accepted += 1
        if (index+1) % 50 == 0:
            print('ROW ORBITS', index+1, '/', len(entries), 'ROWS', len(rows),
                  'SECONDS', time.monotonic()-start, flush=True)
    print('BEGIN RREF', len(rows), width+1, 'SECONDS', time.monotonic()-start, flush=True)
    rr, rank = nmod_mat(rows, PRIME).rref()
    pivots = [next(j for j in range(width+1) if rr[i, j]) for i in range(rank)]
    augmented = width in pivots
    result = dict(status='MODULAR_TWO_PAGE_TRIANGLE_GRAFT_DIAGNOSTIC', n=7,
                  source_inventory_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  descriptors=descriptors, ranks=[rank-int(augmented), rank], prime=PRIME,
                  points=points, modular_rows=rows, row_plan=entries,
                  matrix_entry_budget=MAX_ENTRIES,
                  scope=inventory['scope'])
    dest = HERE/'overnight_upper_triangle_graft_probe_7.json'
    dest.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('GRAFT RANKS', result['ranks'], 'SECONDS', time.monotonic()-start, flush=True)
    if not augmented:
        coefficients = [Q(0)]*width
        for i, pivot in enumerate(pivots):
            value = base.ratrec((14*int(rr[i, width])) % PRIME, PRIME)
            coefficients[pivot] = None if value is None else value/14
        result['rational_reconstruction_failures'] = sum(v is None for v in coefficients)
        if all(v is not None for v in coefficients):
            result['candidate_coefficients'] = list(map(str, coefficients))
            combined = defaultdict(lambda: defaultdict(Q))
            for coefficient, column in zip(coefficients, columns):
                if coefficient:
                    for plane, expression in column.items():
                        for key, value in expression.items():
                            combined[plane][key] += coefficient*value
            for plane, expression in wanted.items():
                for key, value in expression.items():
                    combined[plane][key] -= value
            gate = base.Verifier(600)
            passed = []
            for entry in entries:
                plane = entry['plane']
                if not gate.check(combined.get(plane, {})):
                    break
                passed.append(plane)
            result['exact_plane_orbits_checked'] = passed
            if len(passed) == len(entries):
                result['status'] = 'EXACT_TWO_PAGE_TRIANGLE_GRAFT_BOUNDARY_IDENTITY'
    result['seconds'] = time.monotonic()-start
    dest.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('DONE', result['status'], 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
