#!/usr/bin/env python3
"""Exact rational reconstruction and equivariant hyperplane gate for S6 control."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib, json, math, time
from flint import fmpq_mat, nmod_mat
import overnight_upper_triangle_attachments as producer
import overnight_upper_product_family as base

HERE = Path(__file__).parent


def evaluate(expression, point):
    result = Q(0)
    for (num, power, denominator), coefficient in expression.items():
        value = coefficient * (sum(a*b for a, b in zip(num[:-1], point)) + num[-1]) ** power
        for form, multiplicity in denominator:
            value /= (sum(a*b for a, b in zip(form[:-1], point)) + form[-1]) ** multiplicity
        result += value
    return result


def plane_orbit(plane):
    values = sorted(plane)
    positive = [v-values[0] for v in values]
    common = math.gcd(*positive)
    positive = tuple(v//common for v in positive)
    negative = tuple(positive[-1]-v for v in reversed(positive))
    return min(positive, negative)


def main():
    start = time.monotonic()
    source = HERE / 'overnight_upper_triangle_attachments_6.json'
    data = json.loads(source.read_text())
    width = len(data['descriptors'])
    rows = data['modular_rows']
    prime = data['prime']
    rr, rank = nmod_mat(rows, prime).rref()
    pivots = [next(j for j in range(width+1) if rr[i, j]) for i in range(rank)]
    assert width not in pivots
    transpose = [[row[j] for row in rows] for j in pivots]
    tr, rowrank = nmod_mat(transpose, prime).rref()
    assert rowrank == rank
    selected = [next(j for j in range(len(rows)) if tr[i, j]) for i in range(rank)]
    descriptors = [data['descriptors'][j] for j in pivots]
    base.raw_chain = producer.raw_chain
    base.group = lambda arity: list(permutations(range(arity)))
    columns = [base.expression(base.sym_chain(6, descriptor)) for descriptor in descriptors]
    wanted = base.target(6)
    exact_rows = []
    for idx in selected:
        plane, point = data['points'][idx]
        plane = tuple(plane)
        exact_rows.append([evaluate(column.get(plane, {}), point) for column in columns]
                          + [evaluate(wanted.get(plane, {}), point)])
    matrix = fmpq_mat([[str(v) for v in row[:-1]] for row in exact_rows])
    target = fmpq_mat([[str(row[-1])] for row in exact_rows])
    solution = matrix.solve(target)
    coefficients = [Q(str(solution[i, 0])) for i in range(rank)]
    print('EXACT SOLUTION', rank, 'SUPPORT', sum(bool(v) for v in coefficients),
          'MAX BITS', max(max(abs(c.numerator).bit_length(), c.denominator.bit_length()) for c in coefficients),
          'SECONDS', time.monotonic()-start, flush=True)
    planes = sorted(set(wanted) | {p for column in columns for p in column})
    representatives = {}
    for plane in planes:
        representatives.setdefault(plane_orbit(plane), plane)
    verifier = base.Verifier(1000)
    checked = []
    for orbit, plane in sorted(representatives.items()):
        expression = defaultdict(Q)
        for coefficient, column in zip(coefficients, columns):
            for key, value in column.get(plane, {}).items():
                expression[key] += coefficient * value
        for key, value in wanted.get(plane, {}).items():
            expression[key] -= value
        assert verifier.check(expression), ('failed exact plane', plane)
        checked.append(dict(orbit=orbit, plane=plane))
        print('EXACT PLANE ORBIT', len(checked), '/', len(representatives),
              'SECONDS', time.monotonic()-start, flush=True)
    result = dict(status='EXACT_FULL_S6_TRIANGLE_ATTACHMENT_BOUNDARY_IDENTITY', n=6,
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  source_columns=pivots, source_rows=selected, descriptors=descriptors,
                  coefficients=list(map(str, coefficients)),
                  exact_minor=[[str(v) for v in row] for row in exact_rows],
                  plane_orbits_checked=checked, full_plane_count=len(planes),
                  symmetry='Each column is the alternating full S6 sum of a cubical cycle. Supporting hyperplanes are classified up to permutation, common coordinate shift, and nonzero scaling of the normal. Vanishing on one representative propagates to its entire orbit.',
                  scope='Necessary full permutation control only. No fixed cyclic-order or uniform sufficiency claim.',
                  seconds=time.monotonic()-start)
    (HERE/'overnight_upper_triangle_attachment_exact_6.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('DONE', result['status'], 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
