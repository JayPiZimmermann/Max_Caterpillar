#!/usr/bin/env python3
"""Five global translation states for the compact whole-cycle ear recursion."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib, json, random, time
from flint import nmod_mat
import overnight_upper_triangle_attachments as attachment
import overnight_upper_triangle_fixed as fixed
import overnight_upper_product_family as base

HERE = Path(__file__).parent


def old_cycle(witness):
    base.raw_chain = attachment.raw_chain
    base.group = fixed.group
    chain = defaultdict(Q)
    for item in witness['selected']:
        coefficient = Q(item['coefficient'])
        for (head, edges), value in base.sym_chain(6, item['descriptor']).items():
            chain[(head+(0,), tuple(e+(0,) for e in edges))] += coefficient*value
    return {k: v for k, v in chain.items() if v}


def symmetrize(chain):
    out = defaultdict(Q)
    for pi in fixed.group(7):
        def image(vector):
            result = [0]*7
            for i, value in enumerate(vector):
                result[pi[i]] = value
            return tuple(result)
        for (head, edges), coefficient in chain.items():
            item = base.normalize_cube(image(head), [image(e) for e in edges],
                                       coefficient*base.parity(pi))
            if item:
                out[item[0]] += item[1]
    return {k: v for k, v in out.items() if v}


def column(old, translation, root, sign):
    other = [i for i in (0, 5, 6) if i != root]
    ear = base.triangle(7, root, *other, sign)
    chain = defaultdict(Q)
    for (head, edges), coefficient in old.items():
        head = base.addv(head, translation)
        for ear_head, vector, c in ear:
            item = base.normalize_cube(base.addv(head, ear_head), edges+(vector,), coefficient*c)
            if item:
                chain[item[0]] += item[1]
    return base.expression(symmetrize({k: v for k, v in chain.items() if v}))


def main():
    start = time.monotonic()
    source = HERE/'overnight_upper_two_page_witness_6.json'
    witness = json.loads(source.read_text())
    old = old_cycle(witness)
    translations = [(0,)*7]
    for neighbor in (0, 5):
        direction = base.diff(7, 6, neighbor)
        translations += [direction, tuple(-v for v in direction)]
    descriptors = list(product(translations, (0, 5, 6), (-1, 1)))
    columns = []
    for i, (translation, root, sign) in enumerate(descriptors):
        columns.append(column(old, translation, root, sign))
        if (i+1) % 5 == 0:
            print('TRANSLATED EAR COLUMNS', i+1, '/', len(descriptors),
                  'CACHED CUBES', base.cube_kernel.cache_info().currsize,
                  'SECONDS', time.monotonic()-start, flush=True)
    wanted = base.target(7)
    planes = sorted(set(wanted) | {p for c in columns for p in c})
    representatives = {}
    for plane in planes:
        representatives.setdefault(fixed.plane_orbit(plane), plane)
    rng = random.Random(251034)
    rows, points = [], []
    for orbit, plane in sorted(representatives.items()):
        accepted = 0
        while accepted < 3:
            point = tuple(rng.randrange(1, 1000) for _ in range(5))
            try:
                row = [base.evaluate(c.get(plane, {}), point) for c in columns]
                row.append(base.evaluate(wanted.get(plane, {}), point))
            except ZeroDivisionError:
                continue
            rows.append(row)
            points.append((plane, point))
            accepted += 1
    width = len(columns)
    rr, rank = nmod_mat(rows, base.PRIME).rref()
    pivots = [next(j for j in range(width+1) if rr[i, j]) for i in range(rank)]
    augmented = width in pivots
    result = dict(status='MODULAR_WHOLE_CYCLE_TRANSLATED_EAR_DIAGNOSTIC', n=7,
                  descriptors=descriptors, source_witness_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  ranks=[rank-int(augmented), rank], prime=base.PRIME, modular_rows=rows,
                  points=points, plane_count=len(planes), plane_orbit_count=len(representatives),
                  scope='Whole exact N6 two-page cycle, translated by 0 or ±(e6−e0), ±(e6−e5), multiplied by any rooted/reflected exterior-ear triangle, then D7 averaged. A particular 30-state recurrence test only.')
    dest = HERE/'overnight_upper_ear_translations_7.json'
    dest.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('RANKS', result['ranks'], 'PLANE ORBITS', len(representatives),
          'SECONDS', time.monotonic()-start, flush=True)
    gate = base.Verifier(600)

    def check(coefficients, target=False):
        for plane in representatives.values():
            expression = defaultdict(Q)
            for coefficient, c in zip(coefficients, columns):
                if coefficient:
                    for key, value in c.get(plane, {}).items():
                        expression[key] += coefficient*value
            if target:
                for key, value in wanted.get(plane, {}).items():
                    expression[key] -= value
            if not gate.check(expression):
                return False
        return True

    if augmented:
        free = [j for j in range(width) if j not in pivots]
        relations = []
        for j in free:
            coefficients = [Q(0)]*width
            coefficients[j] = Q(1)
            for i, p in enumerate(pivots):
                if p < width:
                    value = base.ratrec(int(rr[i, j]), base.PRIME)
                    assert value is not None
                    coefficients[p] = -value
            assert check(coefficients), ('exact translated relation', j)
            relations.append(list(map(str, coefficients)))
        result['exact_relations'] = relations
        result['status'] = 'EXACT_WHOLE_CYCLE_TRANSLATED_EAR_OBSTRUCTION'
    else:
        coefficients = [Q(0)]*width
        for i, p in enumerate(pivots):
            value = base.ratrec((14*int(rr[i, width])) % base.PRIME, base.PRIME)
            coefficients[p] = None if value is None else value/14
        if all(c is not None for c in coefficients) and check(coefficients, True):
            result['exact_coefficients'] = list(map(str, coefficients))
            result['status'] = 'EXACT_WHOLE_CYCLE_TRANSLATED_EAR_IDENTITY'
    result['seconds'] = time.monotonic()-start
    dest.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('DONE', result['status'], 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
