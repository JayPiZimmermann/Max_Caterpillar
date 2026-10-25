#!/usr/bin/env python3
"""Compact replay bundle for the completed two-page boundary controls.

The large sampled matrices are replaced by sparse full-rank minors and
independent exact rational kernel relations. Replaying evaluates every
stored minor entry from the underlying cubes, then checks all identities.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations, product
from pathlib import Path
import hashlib, json, sys, time
from flint import nmod_mat
import overnight_upper_product_family as base
import overnight_upper_triangle_attachments as attachment
import overnight_upper_triangle_fixed as fixed
import overnight_upper_triangle_attachment_exact as full
import overnight_upper_ear_translations as translated

HERE = Path(__file__).parent
DEST = HERE/'overnight_upper_two_page_bundle.json'


def sparse(row):
    return [[i, str(value)] for i, value in enumerate(row) if Q(str(value))]


def extract():
    cases = []
    for name, sample_name, exact_name, kind in [
        ('one_page_6', 'triangle_fixed_6', 'triangle_fixed_exact_6', 'products'),
        ('ear_7', 'triangle_ear_7', 'triangle_ear_exact_7', 'products'),
        ('translated_ear_7', 'ear_translations_7', 'ear_translations_7', 'translated')]:
        sample_path = HERE/('overnight_upper_'+sample_name+'.json')
        exact_path = HERE/('overnight_upper_'+exact_name+'.json')
        sample = json.loads(sample_path.read_text())
        exact = json.loads(exact_path.read_text())
        rows = sample['modular_rows']
        prime = sample['prime']
        transpose = nmod_mat(rows, prime).transpose()
        reduced, rank = transpose.rref()
        selected = [next(j for j in range(len(rows)) if reduced[i, j]) for i in range(rank)]
        relations = exact.get('relations', exact.get('exact_relations'))
        cases.append(dict(name=name, n=sample['n'], kind=kind,
                          descriptors=sample['descriptors'], prime=prime,
                          ranks=exact['ranks'],
                          minor=[dict(point=sample['points'][j], row=sparse(rows[j])) for j in selected],
                          relations=[sparse(row) for row in relations],
                          scope=sample['scope'],
                          historical_sample_sha256=hashlib.sha256(sample_path.read_bytes()).hexdigest(),
                          historical_exact_sha256=hashlib.sha256(exact_path.read_bytes()).hexdigest()))
    positive = json.loads((HERE/'overnight_upper_triangle_attachment_exact_6.json').read_text())
    full_positive = [dict(coefficient=c, descriptor=d)
                     for c, d in zip(positive['coefficients'], positive['descriptors']) if c != '0']
    result = dict(status='COMPACT_COMPLETED_TWO_PAGE_BOUNDARY_CONTROLS',
                  two_page_positive=json.loads((HERE/'overnight_upper_two_page_witness_6.json').read_text()),
                  full_permutation_positive=full_positive, negative_cases=cases,
                  scope='Exact finite research controls; not a uniform construction or Lean certificate.',
                  omitted='Historical raw matrix receipts are not required for replay.')
    DEST.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('EXTRACTED', DEST.stat().st_size, 'BYTES', flush=True)


def relation_gate(columns, coefficients, n, target=False, full_symmetry=False):
    expression = defaultdict(lambda: defaultdict(Q))
    for coefficient, column in zip(coefficients, columns):
        if coefficient:
            for plane, terms in column.items():
                for key, value in terms.items():
                    expression[plane][key] += coefficient*value
    if target:
        for plane, terms in base.target(n).items():
            for key, value in terms.items():
                expression[plane][key] -= value
    orbit = full.plane_orbit if full_symmetry else fixed.plane_orbit
    representatives = {}
    for plane in expression:
        representatives.setdefault(orbit(plane), plane)
    gate = base.Verifier(300)
    for plane in representatives.values():
        assert gate.check(expression[plane]), ('exact relation', plane)


def signature(column):
    if not column:
        return None
    scale = next(iter(next(iter(column.values())).values()))
    return tuple((p, tuple(sorted((key, value/scale) for key, value in terms.items())))
                 for p, terms in sorted(column.items()))


def replay():
    start = time.monotonic()
    bundle = json.loads(DEST.read_text())
    import overnight_upper_two_page_witness as compact
    base.raw_chain = attachment.raw_chain
    base.group = fixed.group
    columns = []
    coefficients = []
    for selected in bundle['two_page_positive']['selected']:
        assert tuple(selected['page_colors']) == compact.coloring(selected['descriptor'])
        chain = base.sym_chain(6, selected['descriptor'])
        assert not compact.boundary(chain)
        columns.append(base.expression(chain))
        coefficients.append(Q(selected['coefficient']))
    relation_gate(columns, coefficients, 6, target=True)
    print('REPLAY POSITIVE FIXED TWO PAGES', round(time.monotonic()-start, 2), flush=True)
    base.group = lambda n: list(permutations(range(n)))
    columns = [base.expression(base.sym_chain(6, item['descriptor']))
               for item in bundle['full_permutation_positive']]
    relation_gate(columns, [Q(item['coefficient']) for item in bundle['full_permutation_positive']],
                  6, target=True, full_symmetry=True)
    print('REPLAY POSITIVE FULL S6 CONTROL', round(time.monotonic()-start, 2), flush=True)
    for case in bundle['negative_cases']:
        base.group = fixed.group
        base.raw_chain = attachment.raw_chain
        if case['kind'] == 'translated':
            old = translated.old_cycle(bundle['two_page_positive'])
            columns = [translated.column(old, tuple(t), r, s) for t, r, s in case['descriptors']]
        else:
            columns = [base.expression(base.sym_chain(case['n'], d)) for d in case['descriptors']]
        if case['name'] == 'one_page_6':
            _, all_descriptors = fixed.inventory(6)
            all_signatures = {signature(base.expression(base.sym_chain(6, d))) for d in all_descriptors}
            all_signatures.discard(None)
            assert all_signatures == {signature(c) for c in columns}, 'complete one-page coverage'
        elif case['name'] == 'ear_7':
            expected = set()
            for item in bundle['two_page_positive']['selected']:
                for pi in fixed.group(6):
                    old = attachment.image_descriptor(item['descriptor'], pi)
                    for root, sign in product((0, 5, 6), (-1, 1)):
                        descriptor = tuple(sorted(old+(((0, 5, 6), root, sign),)))
                        expected.add(min(attachment.image_descriptor(descriptor, g) for g in fixed.group(7)))
            got = {tuple((tuple(t), r, s) for t, r, s in d) for d in case['descriptors']}
            assert expected == got, 'complete exterior-ear coverage'
        elif case['name'] == 'translated_ear_7':
            translations = [(0,)*7]
            for neighbor in (0, 5):
                direction = base.diff(7, 6, neighbor)
                translations += [direction, tuple(-v for v in direction)]
            assert {(tuple(t), r, s) for t, r, s in case['descriptors']} == set(product(translations, (0, 5, 6), (-1, 1)))
        width = len(columns)
        target = base.target(case['n'])
        rows = []
        for selected in case['minor']:
            plane, point = selected['point']
            plane = tuple(plane)
            row = [base.evaluate(c.get(plane, {}), point, case['prime']) for c in columns]
            row.append(base.evaluate(target.get(plane, {}), point, case['prime']))
            assert sparse(row) == selected['row'], ('minor entry mismatch', case['name'])
            rows.append(row)
        assert nmod_mat(rows, case['prime']).rank() == case['ranks'][1]
        exact_relations = []
        for sparse_relation in case['relations']:
            coefficients = [Q(0)]*width
            for index, value in sparse_relation:
                coefficients[index] = Q(value)
            relation_gate(columns, coefficients, case['n'])
            exact_relations.append([int(c.numerator*pow(c.denominator, -1, case['prime']) % case['prime'])
                                    for c in coefficients])
        assert nmod_mat(exact_relations, case['prime']).rank() == width-case['ranks'][0]
        print('REPLAY NEGATIVE', case['name'], case['ranks'], round(time.monotonic()-start, 2), flush=True)
        base.cube_kernel.cache_clear()
    print('ALL COMPACT BOUNDARY REPLAYS PASS', round(time.monotonic()-start, 2), 'SECONDS', flush=True)


if __name__ == '__main__':
    if '--extract' in sys.argv:
        extract()
    if '--replay' in sys.argv:
        replay()
