#!/usr/bin/env python3
"""Compact exact replay of the complete marked-affine exterior-ear exclusion.

Only selected modular-minor points and row digests, exact rational relations,
model descriptions, and the N6 witness are stored. Replay rebuilds the minors.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib, json, sys, time
from flint import nmod_mat
import overnight_upper_product_family as base
import overnight_upper_triangle_attachments as attachment
import overnight_upper_triangle_fixed as fixed
import overnight_upper_marked_kernel_inventory as marked
import overnight_upper_marked_kernel_probe as lower
import overnight_upper_marked_ear_inventory as upper
import overnight_upper_oriented_products as oriented
from overnight_upper_triangle_two_pages import two_pages
from overnight_upper_modular_cache2 import Evaluator

HERE = Path(__file__).parent
DEST = HERE/'overnight_upper_marked_bundle.json'


def read(name):
    return json.loads((HERE/('overnight_upper_'+name+'.json')).read_text())


def sparse(values):
    return [[j, int(v)] for j, v in enumerate(values) if v]


def row_digest(values):
    return hashlib.sha256(b''.join(int(v).to_bytes(4,'little') for v in values)).hexdigest()


def minor(data):
    rows, prime = data['modular_rows'], data['prime']
    matrix = nmod_mat(rows, prime)
    rr, rank = matrix.rref()
    columns = [next(j for j in range(matrix.ncols()) if rr[i, j]) for i in range(rank)]
    del rr
    selected = nmod_mat([[r[j] for j in columns] for r in rows], prime)
    rr, rank2 = selected.transpose().rref()
    assert rank2 == rank
    row_indices = [next(j for j in range(len(rows)) if rr[i, j]) for i in range(rank)]
    return dict(rank=rank, columns=columns,
                rows=[dict(point=data['points'][i], sha256=row_digest([rows[i][j] for j in columns]))
                      for i in row_indices])


def extract():
    old = read('two_page_bundle')
    inventory = read('marked_kernel_inventory_6')
    sectors = []
    for name in ('minus', 'plus'):
        data = read('marked_kernel_'+name+'_6')
        sectors.append(dict(character=data['character'], descriptors=data['descriptors'],
                            rank=data['rank'], prime=data['prime'], minor=minor(data),
                            relations=data['relations_sparse'],
                            formal_cube_supports=data['formal_cube_supports']))
    output = read('marked_ear_probe_7')
    assert output['status'] == 'EXACT_FULL_MARKED_AFFINE_EAR_OBSTRUCTION'
    result = dict(status='COMPACT_EXACT_COMPLETE_MARKED_AFFINE_EAR_OBSTRUCTION',
                  templates=[r['descriptor'] for r in old['full_permutation_positive']],
                  positive_witness=read('two_page_witness_6'),
                  raw_descriptors=inventory['raw_descriptors'],
                  reflection_orbit_representatives=inventory['reflection_orbit_representatives'],
                  sectors=sectors, output_inventory=read('marked_ear_inventory_7'),
                  output=dict(ranks=output['ranks'], prime=output['prime'], minor=minor(output),
                              relations=output['exact_relations_sparse']),
                  scope=output['scope'],
                  omitted='Raw sampled matrices are historical search artifacts and are not needed by replay.',
                  historical_sha256={name: hashlib.sha256((HERE/('overnight_upper_'+name+'.json')).read_bytes()).hexdigest()
                                     for name in ['marked_kernel_minus_6','marked_kernel_plus_6','marked_ear_probe_7']})
    DEST.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('EXTRACTED MARKED BUNDLE', DEST.stat().st_size, 'BYTES', flush=True)


def relation_expression(columns, coefficients):
    expression = defaultdict(lambda: defaultdict(Q))
    for index, coefficient in coefficients:
        coefficient = Q(coefficient)
        for plane, terms in columns[index].items():
            for key, value in terms.items():
                expression[plane][key] += coefficient*value
    return expression


def exact_gate(expression, orbit, gate):
    representatives = {}
    for plane in expression:
        representatives.setdefault(orbit(plane), plane)
    for plane in representatives.values():
        assert gate.check(expression[plane]), ('exact rational identity', plane)


def check_minor(data, columns, target=None):
    prime = data['prime']
    selected = data['minor']
    evaluate = Evaluator()
    rows = []
    for record in selected['rows']:
        plane, point = record['point']
        plane = tuple(plane)
        row = [evaluate((columns[j] if j < len(columns) else target).get(plane, {}), point, prime)
               for j in selected['columns']]
        assert row_digest(row) == record['sha256'], 'independently recomputed minor row'
        rows.append(row)
    assert nmod_mat(rows, prime).rank() == selected['rank']


def relation_rank(relations, width, prime):
    rows = []
    for relation in relations:
        row = [0]*width
        for j, value in relation:
            q = Q(value)
            row[j] = q.numerator*pow(q.denominator, -1, prime) % prime
        rows.append(row)
    return nmod_mat(rows, prime).rank()


def check_coverage(bundle):
    raw = set()
    for template in bundle['templates']:
        for pi in permutations(range(6)):
            descriptor = attachment.image_descriptor(template, pi)
            if two_pages([t for t, _, _ in descriptor]):
                raw.add(descriptor)
    representatives = sorted({min(d, attachment.image_descriptor(d, marked.REFLECTION)) for d in raw})
    assert len(raw) == bundle['raw_descriptors'] == 2052
    assert len(representatives) == bundle['reflection_orbit_representatives'] == 1026
    for sector in bundle['sectors']:
        seen, expected = set(), []
        for descriptor in representatives:
            chain = marked.projected_chain(descriptor, sector['character'])
            if chain:
                scale = next(iter(chain.values()))
                signature = tuple(sorted((key, value/scale) for key, value in chain.items()))
                if signature not in seen:
                    seen.add(signature)
                    expected.append(descriptor)
        assert expected == [upper.descriptor_tuple(d) for d in sector['descriptors']]


def check_output_inventory(bundle):
    """Regenerate every retained and discarded attachment channel algebraically."""
    candidates = []
    for sign in (-1, 1):
        expression = defaultdict(Q)
        for item in bundle['positive_witness']['selected']:
            d = upper.descriptor_tuple(item['descriptor'])
            for pi in fixed.group(6):
                image, old_phase = oriented.image_with_phase(d, pi)
                target, phase = oriented.canonical(7, image+(((0,5,6),0,sign),))
                if phase:
                    expression[target] += Q(item['coefficient'])*base.parity(pi)*old_phase*phase
        candidates.append((dict(kind='particular_lift',character=-1,root=0,sign=sign),
                           {k:v for k,v in expression.items() if v}))
    for sector in bundle['sectors']:
        chi = sector['character']
        descriptors = [upper.descriptor_tuple(d) for d in sector['descriptors']]
        for d in descriptors:
            for sign in (-1,1):
                left = upper.primitive_map(d,chi,0,sign)
                assert upper.primitive_map(d,chi,5,sign) == {k:-chi*v for k,v in left.items()}
                if chi == -1:
                    assert not upper.primitive_map(d,chi,6,sign)
        for state, (relation, support) in enumerate(zip(sector['relations'],sector['formal_cube_supports'])):
            if not support:
                continue
            for root in ((0,) if chi == -1 else (0,6)):
                for sign in (-1,1):
                    expression = defaultdict(Q)
                    for index, coefficient in relation:
                        for target,value in upper.primitive_map(descriptors[index],chi,root,sign).items():
                            expression[target] += Q(coefficient)*value
                    candidates.append((dict(kind='kernel',character=chi,state=state,root=root,sign=sign),
                                       {k:v for k,v in expression.items() if v}))
    distinct, seen, quotient = [], {}, []
    for label, expression in candidates:
        if not expression:
            quotient.append(dict(source=label,column=None))
            continue
        scale = expression[min(expression)]
        signature = tuple(sorted((k,v/scale) for k,v in expression.items()))
        if signature not in seen:
            seen[signature] = len(distinct)
            distinct.append((label,expression))
        col = seen[signature]
        reference = distinct[col][1]
        quotient.append(dict(source=label,column=col,scale=str(scale/reference[min(reference)])))
    primitives = sorted({p for _,expression in distinct for p in expression})
    index = {p:i for i,p in enumerate(primitives)}
    columns = [dict(label=label,coefficients=[[index[p],str(c)] for p,c in sorted(expression.items())])
               for label,expression in distinct]
    got = bundle['output_inventory']
    assert primitives == [upper.descriptor_tuple(d) for d in got['primitive_descriptors']]
    assert columns == got['columns']
    assert quotient == got['source_quotient']


def replay():
    start = time.monotonic()
    bundle = json.loads(DEST.read_text())
    base.raw_chain = attachment.raw_chain
    base.group = fixed.group
    check_coverage(bundle)
    print('MARKED COMPLETE SOURCE COVERAGE PASS', round(time.monotonic()-start,2), flush=True)
    # Recheck the affine base point rather than trusting a status string.
    expression = defaultdict(lambda:defaultdict(Q))
    for item in bundle['positive_witness']['selected']:
        for plane,terms in base.expression(base.sym_chain(6,item['descriptor'])).items():
            for key,value in terms.items():
                expression[plane][key] += Q(item['coefficient'])*value
    for plane,terms in base.target(6).items():
        for key,value in terms.items():
            expression[plane][key] -= value
    exact_gate(expression,fixed.plane_orbit,base.Verifier(120))
    for sector in bundle['sectors']:
        chi = sector['character']
        chains = [marked.projected_chain(d,chi) for d in sector['descriptors']]
        columns = [base.expression(c) for c in chains]
        check_minor(sector,columns)
        assert sector['minor']['rank'] == sector['rank']
        gate = base.Verifier(300)
        for relation, support in zip(sector['relations'],sector['formal_cube_supports']):
            chain = defaultdict(Q)
            for index,coefficient in relation:
                for key,value in chains[index].items():
                    chain[key] += Q(coefficient)*value
            chain = {k:v for k,v in chain.items() if v}
            assert len(chain) == support
            exact_gate(base.expression(chain),lower.plane_orbit,gate)
        assert relation_rank(sector['relations'],len(columns),sector['prime']) == len(columns)-sector['rank']
        print('MARKED LOWER SECTOR EXACT',chi,sector['rank'],round(time.monotonic()-start,2),flush=True)
    del chains,columns
    check_output_inventory(bundle)
    print('MARKED ALL ATTACHMENT CHANNELS PASS',round(time.monotonic()-start,2),flush=True)
    primitives = []
    for i,d in enumerate(bundle['output_inventory']['primitive_descriptors']):
        primitives.append(base.expression(base.sym_chain(7,d)))
        if (i+1)%500 == 0:
            print('MARKED REPLAY PRODUCTS',i+1,round(time.monotonic()-start,2),flush=True)
    maps = bundle['output_inventory']['columns']
    output = bundle['output']
    target = base.target(7)
    evaluate = Evaluator()
    rows = []
    prime = output['prime']
    # Never materialize all output rational expressions simultaneously.
    for record in output['minor']['rows']:
        plane,point = record['point']
        plane = tuple(plane)
        values = {}
        row = []
        for index in output['minor']['columns']:
            if index == len(maps):
                row.append(evaluate(target.get(plane,{}),point,prime))
                continue
            value = 0
            for j,coefficient in maps[index]['coefficients']:
                if j not in values:
                    values[j] = evaluate(primitives[j].get(plane,{}),point,prime)
                c = Q(coefficient)
                value += values[j]*c.numerator*pow(c.denominator,-1,prime)
            row.append(value%prime)
        assert row_digest(row) == record['sha256'], 'complete output minor row'
        rows.append(row)
    assert nmod_mat(rows,prime).rank() == output['ranks'][1] == 781
    print('MARKED OUTPUT AUGMENTED MINOR PASS',round(time.monotonic()-start,2),flush=True)
    gate = base.Verifier(550)
    for count,relation in enumerate(output['relations']):
        coefficients = defaultdict(Q)
        for index,coefficient in relation:
            for j,value in maps[index]['coefficients']:
                coefficients[j] += Q(coefficient)*Q(value)
        expression = relation_expression(primitives,[(j,c) for j,c in coefficients.items() if c])
        exact_gate(expression,fixed.plane_orbit,gate)
        if (count+1)%50 == 0:
            print('MARKED OUTPUT EXACT RELATIONS',count+1,round(time.monotonic()-start,2),flush=True)
    assert relation_rank(output['relations'],len(maps),prime) == len(maps)-output['ranks'][0] == 348
    print('COMPLETE MARKED AFFINE EAR EXCLUSION REPLAY PASS',round(time.monotonic()-start,2),'SECONDS',flush=True)


if __name__ == '__main__':
    if '--extract' in sys.argv:
        extract()
    if '--replay' in sys.argv:
        replay()
