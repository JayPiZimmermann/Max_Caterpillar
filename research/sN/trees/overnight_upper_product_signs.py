#!/usr/bin/env python3
"""Exact S6 control with independently reflected triangle factors.

This is the complete full-label permutation closure of products of three
triangle boundaries sharing a ghost vertex, with the three nonghost edges
forming a two-component forest. Each factor may be independently reflected.
No noncrossing restriction is imposed, making failure a necessary control
for every fixed-order subfamily of this particular product construction.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations, product
from pathlib import Path
import hashlib, json, random, time
from flint import nmod_mat
import overnight_upper_product_family as base

HERE = Path(__file__).parent


def signed_chain(n, descriptor):
    root, edges, signs = descriptor
    out = defaultdict(Q)
    factors = [base.triangle(n, root, u, v, sign)
               for (u, v), sign in zip(edges, signs)]
    for choices in product(*factors):
        h = (0,) * n
        c = 1
        vectors = []
        for head, vector, coefficient in choices:
            h = base.addv(h, head)
            vectors.append(vector)
            c *= coefficient
        item = base.normalize_cube(h, vectors, c)
        if item:
            out[item[0]] += item[1]
    return {k: v for k, v in out.items() if v}


def main():
    start = time.monotonic()
    n = 6
    shapes = [((2, 3), (2, 4), (2, 5)),
              ((2, 3), (3, 4), (4, 5)),
              ((1, 2), (3, 4), (4, 5))]
    descriptors = [(0, edges, signs) for edges in shapes
                   for signs in product((-1, 1), repeat=3)]
    base.raw_chain = signed_chain
    base.group = lambda arity: list(permutations(range(arity)))
    columns = [base.expression(base.sym_chain(n, d)) for d in descriptors]
    wanted = base.target(n)
    planes = sorted(set(wanted) | {p for e in columns for p in e})
    width = len(columns)
    print('INVENTORY', width, 'SIGNED SHAPE COLUMNS', len(planes),
          'SPAN PLANES', 'SECONDS', time.monotonic() - start, flush=True)
    rng = random.Random(251030)
    rows, points = [], []
    for plane in planes:
        accepted = 0
        while accepted < 4:
            point = tuple(rng.randrange(1, 1000) for _ in range(n - 2))
            try:
                row = [base.evaluate(e.get(plane, {}), point) for e in columns]
                row.append(base.evaluate(wanted.get(plane, {}), point))
            except ZeroDivisionError:
                continue
            points.append((plane, point))
            rows.append(row)
            accepted += 1
    rr, rank = nmod_mat(rows, base.PRIME).rref()
    pivots = [next(j for j in range(width + 1) if rr[i, j]) for i in range(rank)]
    augmented = width in pivots
    ranks = [rank - int(augmented), rank]
    result = dict(status='MODULAR_INDEPENDENT_TRIANGLE_SIGN_DIAGNOSTIC', n=n,
                  descriptors=descriptors, permutations=720, planes=planes,
                  points=points, prime=base.PRIME, modular_rows=rows, ranks=ranks,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  kernel_producer_sha256=hashlib.sha256(Path(base.__file__).read_bytes()).hexdigest(),
                  scope='All two-component forest products of independently positive or reflected triangle boundaries on six labels, each with a common ghost vertex, under the full S6 action. No noncrossing restriction.')
    print('RANKS', ranks, 'SECONDS', time.monotonic() - start, flush=True)
    verifier = base.Verifier(240)

    def check(coefficients, subtract_target=False):
        for plane in planes:
            expression = defaultdict(Q)
            for coefficient, column in zip(coefficients, columns):
                if coefficient:
                    for key, value in column.get(plane, {}).items():
                        expression[key] += coefficient * value
            if subtract_target:
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
            print('EXACT KERNEL', len(relations), '/', len(free), flush=True)
        result['exact_relations'] = relations
        result['status'] = 'EXACT_INDEPENDENT_TRIANGLE_SIGN_OBSTRUCTION'
    else:
        coefficients = [Q(0)] * width
        for i, pivot in enumerate(pivots):
            coefficients[pivot] = base.ratrec(int(rr[i, width]), base.PRIME)
        if all(c is not None for c in coefficients) and check(coefficients, True):
            result['exact_coefficients'] = list(map(str, coefficients))
            result['status'] = 'EXACT_INDEPENDENT_TRIANGLE_SIGN_IDENTITY'
    result['seconds'] = time.monotonic() - start
    (HERE / 'overnight_upper_product_signs_6.json').write_text(
        json.dumps(result, separators=(',', ':')) + '\n')
    print('DONE', result['status'], 'RANKS', ranks, 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
