#!/usr/bin/env python3
"""Triangulation product cycles with an attachment vertex in each factor.

Unlike the closed common-ghost route, each triangle is translated so its
own attachment vertex is at zero. These translations change the coned
class. Catalan triangulations, one omitted face, and six choices per kept
triangle give an exponential-size uniform candidate, not a theorem.
"""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
import hashlib, json, random, sys, time
from flint import nmod_mat
import overnight_upper_product_family as base

HERE = Path(__file__).parent


@lru_cache(None)
def triangulations(vertices):
    if len(vertices) < 3:
        return ((),)
    out = []
    a, b = vertices[0], vertices[-1]
    for k in range(1, len(vertices) - 1):
        triangle = tuple(sorted((a, vertices[k], b)))
        for left in triangulations(vertices[:k + 1]):
            for right in triangulations(vertices[k:]):
                out.append(tuple(sorted(left + right + (triangle,))))
    return tuple(sorted(set(out)))


def image_shape(shape, pi):
    return tuple(sorted(tuple(sorted(pi[v] for v in triangle)) for triangle in shape))


def image_descriptor(descriptor, pi):
    return tuple(sorted((tuple(sorted(pi[v] for v in triangle)), pi[root], sign)
                        for triangle, root, sign in descriptor))


def inventory(n):
    group = list(permutations(range(n)))
    shapes = set()
    tris = triangulations(tuple(range(n)))
    for triangulation in tris:
        for omit in range(len(triangulation)):
            shape = triangulation[:omit] + triangulation[omit + 1:]
            shapes.add(min(image_shape(shape, pi) for pi in group))
    descriptors = set()
    for shape in sorted(shapes):
        automorphisms = [pi for pi in group if image_shape(shape, pi) == shape]
        for choices in product(*[tuple(product(triangle, (-1, 1))) for triangle in shape]):
            descriptor = tuple((triangle, root, sign) for triangle, (root, sign) in zip(shape, choices))
            descriptors.add(min(image_descriptor(descriptor, pi) for pi in automorphisms))
    return dict(n=n, triangulations=len(tris), shapes=sorted(shapes),
                descriptors=sorted(descriptors), permutations=len(group),
                scope='Full S_N closure of products of N−3 triangle boundaries selected by omitting one face of an N-gon triangulation. Each triangle has its own attachment vertex and reflection.')


def raw_chain(n, descriptor):
    factors = []
    for triangle, root, sign in descriptor:
        u, v = [i for i in triangle if i != root]
        factors.append(base.triangle(n, root, u, v, sign))
    out = defaultdict(Q)
    for choices in product(*factors):
        h = (0,) * n
        coefficient = 1
        vectors = []
        for head, vector, c in choices:
            h = base.addv(h, head)
            vectors.append(vector)
            coefficient *= c
        item = base.normalize_cube(h, vectors, coefficient)
        if item:
            out[item[0]] += item[1]
    return {k: v for k, v in out.items() if v}


def main(probe=False):
    start = time.monotonic()
    n = 6
    inv = inventory(n)
    print('INVENTORY', inv['triangulations'], 'TRIANGULATIONS', len(inv['shapes']),
          'SHAPES', len(inv['descriptors']), 'ATTACHMENT ORBITS', flush=True)
    result = dict(status='COMPLETE_TRIANGLE_ATTACHMENT_INVENTORY', **inv,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if probe:
        base.raw_chain = raw_chain
        base.group = lambda arity: list(permutations(range(arity)))
        columns = []
        kept = []
        for i, descriptor in enumerate(inv['descriptors']):
            column = base.expression(base.sym_chain(n, descriptor))
            columns.append(column)
            kept.append(descriptor)
            if (i + 1) % 40 == 0:
                print('COLUMNS', i + 1, 'SECONDS', time.monotonic() - start, flush=True)
        wanted = base.target(n)
        planes = sorted(set(wanted) | {p for c in columns for p in c})
        width = len(columns)
        rng = random.Random(251031)
        rows, points = [], []
        for plane in planes:
            accepted = 0
            while accepted < 4:
                point = tuple(rng.randrange(1, 1000) for _ in range(n - 2))
                try:
                    row = [base.evaluate(c.get(plane, {}), point) for c in columns]
                    row.append(base.evaluate(wanted.get(plane, {}), point))
                except ZeroDivisionError:
                    continue
                rows.append(row)
                points.append((plane, point))
                accepted += 1
        rr, rank = nmod_mat(rows, base.PRIME).rref()
        pivots = [next(j for j in range(width + 1) if rr[i, j]) for i in range(rank)]
        augmented = width in pivots
        result.update(status='MODULAR_TRIANGLE_ATTACHMENT_DIAGNOSTIC',
                      ranks=[rank - int(augmented), rank], planes=planes,
                      points=points, prime=base.PRIME, modular_rows=rows)
        print('RANKS', result['ranks'], 'PLANES', len(planes), 'SECONDS', time.monotonic() - start, flush=True)
        verifier = base.Verifier(600)

        def check(coefficients, target=False):
            for plane in planes:
                expression = defaultdict(Q)
                for coefficient, column in zip(coefficients, columns):
                    if coefficient:
                        for key, value in column.get(plane, {}).items():
                            expression[key] += coefficient * value
                if target:
                    for key, value in wanted.get(plane, {}).items():
                        expression[key] -= value
                if not verifier.check(expression):
                    return False
            return True

        if augmented:
            ordinary = [p for p in pivots if p < width]
            free = [j for j in range(width) if j not in ordinary]
            relations = []
            for j in free:
                coefficients = [Q(0)] * width
                coefficients[j] = Q(1)
                for i, pivot in enumerate(pivots):
                    if pivot < width:
                        value = base.ratrec(int(rr[i, j]), base.PRIME)
                        assert value is not None, ('reconstruction', j, pivot)
                        coefficients[pivot] = -value
                assert check(coefficients), ('exact kernel failed', j)
                relations.append(list(map(str, coefficients)))
                if len(relations) % 20 == 0:
                    print('EXACT KERNELS', len(relations), '/', len(free), flush=True)
            result['exact_relations'] = relations
            result['status'] = 'EXACT_TRIANGLE_ATTACHMENT_OBSTRUCTION'
        else:
            coefficients = [Q(0)] * width
            for i, pivot in enumerate(pivots):
                coefficients[pivot] = base.ratrec(int(rr[i, width]), base.PRIME)
            if all(c is not None for c in coefficients) and check(coefficients, True):
                result['exact_coefficients'] = list(map(str, coefficients))
                result['status'] = 'EXACT_TRIANGLE_ATTACHMENT_BOUNDARY_IDENTITY'
    result['seconds'] = time.monotonic() - start
    name = 'overnight_upper_triangle_attachments_6' + ('' if probe else '_inventory') + '.json'
    (HERE / name).write_text(json.dumps(result, separators=(',', ':')) + '\n')
    print('DONE', result['status'], 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main('--probe' in sys.argv)
