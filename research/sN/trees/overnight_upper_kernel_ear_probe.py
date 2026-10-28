#!/usr/bin/env python3
"""Extend the full verified N6 affine lift space by all six exterior ears."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib, json, random, time
from flint import nmod_mat
import overnight_upper_boundary_kernel_states as states
import overnight_upper_ear_translations as ear
import overnight_upper_triangle_fixed as fixed
import overnight_upper_product_family as base
from overnight_upper_modular_cache import Evaluator

HERE = Path(__file__).parent
PRIME = 1000000007


def main():
    start = time.monotonic()
    source = HERE/'overnight_upper_boundary_kernel_states_6.json'
    data = json.loads(source.read_text())
    assert data['status'] == 'EXACT_TWO_PAGE_CONING_KERNEL_STATE_SPACE'
    smaller = states.build_states(data)
    retained = [i for i, chain in enumerate(smaller) if chain]
    old = {i: {(head+(0,), tuple(e+(0,) for e in edges)): c
               for (head, edges), c in smaller[i].items()} for i in retained}
    descriptors = list(product(retained, (0, 5, 6), (-1, 1)))
    columns = []
    for index, (state, root, sign) in enumerate(descriptors):
        columns.append(ear.column(old[state], (0,)*7, root, sign))
        if (index+1) % 12 == 0:
            print('KERNEL EAR COLUMNS', index+1, '/', len(descriptors),
                  'CACHED CUBES', base.cube_kernel.cache_info().currsize,
                  'SECONDS', time.monotonic()-start, flush=True)
    target = base.target(7)
    planes = sorted(set(target) | {p for c in columns for p in c})
    representatives = {}
    for plane in planes:
        representatives.setdefault(fixed.plane_orbit(plane), plane)
    rows, points = [], []
    evaluate = Evaluator()
    rng = random.Random(251037)
    for plane in representatives.values():
        active = sum(bool(column.get(plane)) for column in columns)
        quota = min(active+4, 128 if target.get(plane) else 32)
        accepted = 0
        while accepted < quota:
            point = tuple(rng.randrange(1, 2000) for _ in range(5))
            try:
                row = [evaluate(c.get(plane, {}), point, PRIME) for c in columns]
                row.append(evaluate(target.get(plane, {}), point, PRIME))
            except ZeroDivisionError:
                continue
            rows.append(row)
            points.append((plane, point))
            accepted += 1
    width = len(columns)
    rr, rank = nmod_mat(rows, PRIME).rref()
    pivots = [next(j for j in range(width+1) if rr[i, j]) for i in range(rank)]
    augmented = width in pivots
    result = dict(status='MODULAR_FULL_AFFINE_LIFT_SPACE_EAR_DIAGNOSTIC', n=7,
                  source_states_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  descriptors=descriptors, omitted_formally_zero_states=[i for i in range(len(smaller)) if i not in retained],
                  ranks=[rank-int(augmented), rank], prime=PRIME,
                  points=points, modular_rows=rows, plane_count=len(planes),
                  plane_orbit_count=len(representatives),
                  scope='The fixed exact N6 two-page lift and its complete 37-dimensional D6-averaged coning-kernel state space, each multiplied by all six exterior-ear attachment/reflection states and D7 averaged. No unsymmetrized kernel or non-ear grafts are included.')
    dest = HERE/'overnight_upper_kernel_ear_probe_7.json'
    dest.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('KERNEL EAR RANKS', result['ranks'], 'ROWS', len(rows),
          'SECONDS', time.monotonic()-start, flush=True)
    gate = base.Verifier(700)

    def check(coefficients, subtract_target=False):
        expression = defaultdict(lambda: defaultdict(Q))
        for coefficient, c in zip(coefficients, columns):
            if coefficient:
                for plane, terms in c.items():
                    for key, value in terms.items():
                        expression[plane][key] += coefficient*value
        if subtract_target:
            for plane, terms in target.items():
                for key, value in terms.items():
                    expression[plane][key] -= value
        return all(gate.check(expression.get(plane, {})) for plane in representatives.values())

    if augmented:
        free = [j for j in range(width) if j not in pivots]
        relations = []
        for j in free:
            coefficients = [Q(0)]*width
            coefficients[j] = Q(1)
            for i, p in enumerate(pivots):
                if p < width:
                    value = base.ratrec(int(rr[i, j]), PRIME)
                    assert value is not None
                    coefficients[p] = -value
            assert check(coefficients), ('exact kernel ear relation', j)
            relations.append([[i, str(c)] for i, c in enumerate(coefficients) if c])
            if len(relations) % 20 == 0:
                print('EXACT KERNEL EAR RELATIONS', len(relations), '/', len(free), flush=True)
        result['exact_relations_sparse'] = relations
        result['status'] = 'EXACT_FULL_AFFINE_LIFT_SPACE_EAR_OBSTRUCTION'
    else:
        coefficients = [Q(0)]*width
        for i, p in enumerate(pivots):
            value = base.ratrec((14*int(rr[i, width])) % PRIME, PRIME)
            coefficients[p] = None if value is None else value/14
        if all(c is not None for c in coefficients) and check(coefficients, True):
            result['exact_coefficients'] = list(map(str, coefficients))
            result['status'] = 'EXACT_FULL_AFFINE_LIFT_SPACE_EAR_IDENTITY'
    result['seconds'] = time.monotonic()-start
    dest.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('DONE', result['status'], 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
