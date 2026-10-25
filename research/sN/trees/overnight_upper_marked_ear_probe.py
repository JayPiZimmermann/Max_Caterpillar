#!/usr/bin/env python3
"""Bounded full marked-affine ear gate using shared oriented product columns."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, random, time
from flint import nmod_mat
import overnight_upper_triangle_attachments as attachment
import overnight_upper_triangle_fixed as fixed
import overnight_upper_product_family as base
from overnight_upper_modular_cache2 import Evaluator

HERE = Path(__file__).parent
PRIME = 1000000007


def main():
    start = time.monotonic()
    source = HERE/'overnight_upper_marked_ear_inventory_7.json'
    data = json.loads(source.read_text())
    base.raw_chain = attachment.raw_chain
    base.group = fixed.group
    primitives = []
    for i, descriptor in enumerate(data['primitive_descriptors']):
        primitives.append(base.expression(base.sym_chain(7, descriptor)))
        if (i+1) % 250 == 0:
            print('MARKED EAR PRODUCTS', i+1, '/', len(data['primitive_descriptors']),
                  'CACHED CUBES', base.cube_kernel.cache_info().currsize,
                  'SECONDS', time.monotonic()-start, flush=True)
    maps = [{int(j): Q(c) for j, c in col['coefficients']} for col in data['columns']]
    reverse = [[] for _ in primitives]
    for i, mapping in enumerate(maps):
        for j, coefficient in mapping.items():
            c = coefficient.numerator*pow(coefficient.denominator, -1, PRIME) % PRIME
            reverse[j].append((i, c))
    target = base.target(7)
    planes = sorted(set(target) | {p for c in primitives for p in c})
    representatives = {}
    for plane in planes:
        representatives.setdefault(fixed.plane_orbit(plane), plane)
    entries = []
    for orbit, plane in sorted(representatives.items()):
        active = [j for j, c in enumerate(primitives) if c.get(plane)]
        outputs = {i for j in active for i, _ in reverse[j]}
        entries.append(dict(orbit=orbit, plane=plane, primitives=active,
                            points=min(len(outputs)+4, 96 if target.get(plane) else 40)))
    width = len(maps)
    cap = min(6000, 8_000_000//(width+1))
    while sum(e['points'] for e in entries) > cap:
        candidate = max((e for e in entries if e['points'] > 3), key=lambda e: e['points'])
        candidate['points'] -= 1
    print('MARKED EAR ROW PLAN', len(planes), 'PLANES', len(entries), 'ORBITS',
          sum(e['points'] for e in entries), 'ROWS', width, 'COLS',
          'SECONDS', time.monotonic()-start, flush=True)
    evaluate = Evaluator()
    rng = random.Random(251043)
    rows, points = [], []
    for index, entry in enumerate(entries):
        plane = entry['plane']
        accepted = 0
        while accepted < entry['points']:
            point = tuple(rng.randrange(1, 2000) for _ in range(5))
            row = [0]*width
            try:
                for j in entry['primitives']:
                    value = evaluate(primitives[j][plane], point, PRIME)
                    if value:
                        for output, coefficient in reverse[j]:
                            row[output] += coefficient*value
                row = [v % PRIME for v in row]
                row.append(evaluate(target.get(plane, {}), point, PRIME))
            except ZeroDivisionError:
                continue
            rows.append(row)
            points.append((plane, point))
            accepted += 1
        if (index+1) % 40 == 0:
            print('MARKED EAR ROW ORBITS', index+1, '/', len(entries),
                  'ROWS', len(rows), 'SECONDS', time.monotonic()-start, flush=True)
    rr, rank = nmod_mat(rows, PRIME).rref()
    pivots = [next(j for j in range(width+1) if rr[i, j]) for i in range(rank)]
    augmented = width in pivots
    result = dict(status='MODULAR_FULL_MARKED_AFFINE_EAR_DIAGNOSTIC', n=7,
                  source_inventory_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  ranks=[rank-int(augmented), rank], prime=PRIME,
                  points=points, modular_rows=rows,
                  row_plan=[{k: v for k, v in e.items() if k != 'primitives'} for e in entries],
                  scope=data['scope'])
    dest = HERE/'overnight_upper_marked_ear_probe_7.json'
    dest.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('MARKED EAR RANKS', result['ranks'], 'SECONDS', time.monotonic()-start, flush=True)
    gate = base.Verifier(550)

    def combine(coefficients):
        result = defaultdict(Q)
        for coefficient, mapping in zip(coefficients, maps):
            if coefficient:
                for j, value in mapping.items():
                    result[j] += coefficient*value
        return {j: c for j, c in result.items() if c}

    def check(coefficients, subtract_target=False):
        combined = combine(coefficients)
        expression = defaultdict(lambda: defaultdict(Q))
        for j, coefficient in combined.items():
            for plane, terms in primitives[j].items():
                for key, value in terms.items():
                    expression[plane][key] += coefficient*value
        if subtract_target:
            for plane, terms in target.items():
                for key, value in terms.items():
                    expression[plane][key] -= value
        return all(gate.check(expression.get(e['plane'], {})) for e in entries)

    if augmented:
        free = [j for j in range(width) if j not in pivots]
        relations = []
        failed = None
        try:
            for j in free:
                coefficients = [Q(0)]*width
                coefficients[j] = Q(1)
                for i, p in enumerate(pivots):
                    if p < width:
                        value = base.ratrec(int(rr[i, j]), PRIME)
                        if value is None:
                            failed = ['rational_reconstruction', j, p]
                            break
                        coefficients[p] = -value
                if failed:
                    break
                if not check(coefficients):
                    failed = ['exact_relation_failed', j]
                    break
                relations.append([[i, str(c)] for i, c in enumerate(coefficients) if c])
                if len(relations) % 25 == 0:
                    print('MARKED EAR EXACT KERNELS', len(relations), '/', len(free),
                          'SECONDS', time.monotonic()-start, flush=True)
        except TimeoutError:
            failed = ['exact_gate_budget']
        result['exact_relations_sparse'] = relations
        result['exact_gate_incomplete_reason'] = failed
        if len(relations) == len(free):
            result['status'] = 'EXACT_FULL_MARKED_AFFINE_EAR_OBSTRUCTION'
    else:
        coefficients = [Q(0)]*width
        for i, p in enumerate(pivots):
            value = base.ratrec((14*int(rr[i, width])) % PRIME, PRIME)
            coefficients[p] = None if value is None else value/14
        result['rational_reconstruction_failures'] = sum(c is None for c in coefficients)
        if all(c is not None for c in coefficients):
            result['candidate_coefficients'] = list(map(str, coefficients))
            try:
                if check(coefficients, True):
                    result['status'] = 'EXACT_FULL_MARKED_AFFINE_EAR_BOUNDARY_IDENTITY'
            except TimeoutError:
                result['exact_gate_incomplete_reason'] = ['exact_gate_budget']
    result['seconds'] = time.monotonic()-start
    dest.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('DONE', result['status'], 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
