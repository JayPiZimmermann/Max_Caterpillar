#!/usr/bin/env python3
"""Cheap coefficient-rule test motivated by Eulerian plane-tree weights.

This tests a proposed evaluation of a known abstract tree recurrence. It
does not assume any map from Lie idempotents to the maximum kernel.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import hashlib, json, math, random, time
from flint import fmpq_mat
from overnight_upper_interval_states import pruefer, crosses
from overnight_upper_interval_polynomial import add, mul, descriptors

HERE = Path(__file__).parent


def discrete_integral(polynomial):
    remainder = list(polynomial)
    output = [Q(0)]*(len(polynomial)+1)
    for degree in range(len(polynomial)-1, -1, -1):
        coefficient = remainder[degree]/Q(degree+1)
        output[degree+1] = coefficient
        for j in range(degree+1):
            remainder[j] -= coefficient*math.comb(degree+1, j)
    assert not any(remainder)
    return tuple(output)


@lru_cache(None)
def tree_polynomial(children):
    polynomial = [Q(1)]
    for child in children:
        polynomial = mul(polynomial, tree_polynomial(child))
    return discrete_integral(polynomial)


@lru_cache(None)
def rooted_trees(n):
    output = []
    for edges in pruefer(n):
        if any(crosses(e, f) for e, f in combinations(edges, 2)):
            continue
        adjacency = [[] for _ in range(n)]
        for u, v in edges:
            adjacency[u].append(v)
            adjacency[v].append(u)
        for root in range(n):
            cuts = []
            def visit(v, parent):
                children = []
                vertices = [v]
                for child in adjacency[v]:
                    if child == parent:
                        continue
                    shape, subtree = visit(child, v)
                    children.append(shape)
                    cuts.append(tuple(subtree))
                    vertices.extend(subtree)
                return tuple(sorted(children)), vertices
            shape, _ = visit(root, -1)
            coefficient = tree_polynomial(shape)[1]
            if coefficient:
                output.append((coefficient, tuple(cuts)))
    return tuple(output)


def component(omega, external):
    answer = [Q(0)]*len(omega)
    for coefficient, cuts in rooted_trees(len(omega)):
        polynomial = [coefficient]
        for cut in cuts:
            q = sum(omega[i] for i in cut)
            polynomial = mul(polynomial, [Q(1, q*(q-external)), Q(1, q*(q+external))])
        answer = add(answer, polynomial)
    return answer


def row(omega):
    n = len(omega)
    columns = {key: Q(0) for key in descriptors(n)}
    for size in range(1, n//2+1):
        for shift in range(n):
            cycle = omega[shift:]+omega[:shift]
            left, right = cycle[:size], cycle[size:]
            external = sum(right)
            a, b = component(left, external), component(right, external)
            prefactor = Q(-external)**(n-4)
            for key in columns:
                if key[0] == size:
                    columns[key] += prefactor*a[key[1]]*b[key[2]]
    return list(columns.values())+[Q((-1)**(n-1), math.prod(omega))]


def main():
    start = time.monotonic()
    assert tree_polynomial(()) == (0, 1)
    assert tree_polynomial(((),)) == (0, Q(-1, 2), Q(1, 2))
    assert tree_polynomial(((), ())) == (0, Q(1, 6), Q(-1, 2), Q(1, 3))
    assert tree_polynomial(((), (), ()))[1] == 0
    rng = random.Random(251038)
    records = []
    for n in range(3, 7):
        desc = descriptors(n)
        points, rows = [], []
        while len(rows) < len(desc)+8:
            positive = [rng.randrange(1, 10)]
            while len(positive) < n-1:
                positive.append(3*sum(positive)+rng.randrange(1, 10))
            omega = tuple([-sum(positive)]+positive)
            try:
                values = row(omega)
            except ZeroDivisionError:
                continue
            denominator = math.lcm(*(v.denominator for v in values))
            rows.append([int(v*denominator) for v in values])
            points.append(omega)
        ordinary = fmpq_mat([r[:-1] for r in rows]).rank()
        augmented = fmpq_mat(rows).rank()
        status = 'EVALUATION_DIAGNOSTIC'
        if ordinary == len(desc) and augmented == ordinary+1:
            status = 'EXACT_FULL_COLUMN_EULERIAN_RULE_OBSTRUCTION'
        record = dict(n=n, descriptors=desc, points=points, integer_rows=rows,
                      ranks=[ordinary, augmented], status=status)
        records.append(record)
        print('EULERIAN RULE', n, 'COLS', len(desc), 'RANKS', record['ranks'], status, flush=True)
        if augmented > ordinary:
            break
    result = dict(status='EULERIAN_INTERVAL_COEFFICIENT_RULE_TEST', records=records,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  motivation='Menous–Novelli–Thibon, Tree expansions of some Lie idempotents, DOI 10.5802/alco.373, section 5.2. No representation-theoretic map to these Fourier kernels is asserted.',
                  scope='Each rooted NC tree has weight [t]χ_T(t), with χ_T(t)=sum_{s=0}^{t-1} product_child χ_child(s). Remaining coefficients depend only on component size and positive-away edge counts.',
                  seconds=time.monotonic()-start)
    (HERE/'overnight_upper_interval_eulerian.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
