#!/usr/bin/env python3
"""Fixed cyclic-order triangulation attachment control, with D_N averaging only."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib, json, math, random, time
from flint import nmod_mat
import overnight_upper_triangle_attachments as source
import overnight_upper_product_family as base

HERE = Path(__file__).parent


def group(n):
    return [tuple((sign*i+offset) % n for i in range(n))
            for sign in (1, -1) for offset in range(n)]


def inventory(n):
    permutations = group(n)
    shapes = set()
    for triangulation in source.triangulations(tuple(range(n))):
        for omit in range(len(triangulation)):
            shape = triangulation[:omit]+triangulation[omit+1:]
            shapes.add(min(source.image_shape(shape, pi) for pi in permutations))
    descriptors = set()
    for shape in sorted(shapes):
        automorphisms = [pi for pi in permutations if source.image_shape(shape, pi) == shape]
        for choices in product(*[tuple(product(triangle, (-1, 1))) for triangle in shape]):
            descriptor = tuple((triangle, root, sign) for triangle, (root, sign) in zip(shape, choices))
            descriptors.add(min(source.image_descriptor(descriptor, pi) for pi in automorphisms))
    return sorted(shapes), sorted(descriptors)


def plane_orbit(plane):
    images = []
    for pi in group(len(plane)):
        w = [0] * len(plane)
        for i, value in enumerate(plane):
            w[pi[i]] = value
        w = [v-w[0] for v in w]
        common = math.gcd(*w)
        if next(v for v in w if v) < 0:
            common = -common
        images.append(tuple(v//common for v in w))
    return min(images)


def main(n=6):
    start = time.monotonic()
    shapes, raw = inventory(n)
    print('INVENTORY', n, len(shapes), 'CYCLIC SHAPES', len(raw), 'D_N ATTACHMENT ORBITS', flush=True)
    base.raw_chain = source.raw_chain
    base.group = group
    columns, descriptors, seen = [], [], set()
    for index, descriptor in enumerate(raw):
        column = base.expression(base.sym_chain(n, descriptor))
        if not column:
            continue
        scale = next(iter(next(iter(column.values())).values()))
        signature = tuple((p, tuple(sorted((k, v/scale) for k, v in expr.items())))
                          for p, expr in sorted(column.items()))
        if signature in seen:
            continue
        seen.add(signature)
        columns.append(column)
        descriptors.append(descriptor)
    wanted = base.target(n)
    planes = sorted(set(wanted) | {p for c in columns for p in c})
    width = len(columns)
    print('COLUMNS', width, 'PLANES', len(planes), 'SECONDS', time.monotonic()-start, flush=True)
    assert width*len(planes)*4 < 8_000_000, 'declared matrix entry budget'
    rng = random.Random(251032)
    rows, points = [], []
    for plane in planes:
        accepted = 0
        while accepted < 4:
            point = tuple(rng.randrange(1, 1000) for _ in range(n-2))
            try:
                row = [base.evaluate(c.get(plane, {}), point) for c in columns]
                row.append(base.evaluate(wanted.get(plane, {}), point))
            except ZeroDivisionError:
                continue
            rows.append(row)
            points.append((plane, point))
            accepted += 1
    rr, rank = nmod_mat(rows, base.PRIME).rref()
    pivots = [next(j for j in range(width+1) if rr[i, j]) for i in range(rank)]
    augmented = width in pivots
    result = dict(status='MODULAR_FIXED_ORDER_TRIANGLE_ATTACHMENT_DIAGNOSTIC', n=n,
                  cyclic_shapes=shapes, raw_orbits=len(raw), descriptors=descriptors,
                  ranks=[rank-int(augmented), rank], planes=planes, points=points,
                  prime=base.PRIME, modular_rows=rows,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='One fixed cyclic label order. All polygon triangulations, one omitted triangle, independently chosen attachment vertex and reflection in each retained triangle; only dihedral averaging.')
    print('RANKS', result['ranks'], 'SECONDS', time.monotonic()-start, flush=True)
    if not augmented:
        coefficients = [Q(0)]*width
        for i, pivot in enumerate(pivots):
            # Normalize the orbit sum first, avoiding a gratuitous 2N
            # denominator in bounded single-prime rational reconstruction.
            value = base.ratrec((2*n*int(rr[i, width])) % base.PRIME, base.PRIME)
            coefficients[pivot] = None if value is None else value/(2*n)
        if all(c is not None for c in coefficients):
            result['candidate_coefficients'] = list(map(str, coefficients))
            representatives = {}
            for plane in planes:
                representatives.setdefault(plane_orbit(plane), plane)
            verifier = base.Verifier(1000)
            passed = []
            for orbit, plane in sorted(representatives.items()):
                expression = defaultdict(Q)
                for coefficient, column in zip(coefficients, columns):
                    if coefficient:
                        for key, value in column.get(plane, {}).items():
                            expression[key] += coefficient*value
                for key, value in wanted.get(plane, {}).items():
                    expression[key] -= value
                if not verifier.check(expression):
                    break
                passed.append(dict(orbit=orbit, plane=plane))
            result['exact_plane_orbits_checked'] = passed
            if len(passed) == len(representatives):
                result['status'] = 'EXACT_FIXED_ORDER_TRIANGLE_ATTACHMENT_BOUNDARY_IDENTITY'
    result['seconds'] = time.monotonic()-start
    (HERE/f'overnight_upper_triangle_fixed_{n}.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('DONE', result['status'], 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
