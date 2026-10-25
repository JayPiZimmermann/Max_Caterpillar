#!/usr/bin/env python3
"""Compact eight-product replay, independent of all search matrices."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import hashlib, json, sys, time
import overnight_upper_triangle_attachments as attachment
import overnight_upper_triangle_fixed as fixed
import overnight_upper_product_family as base

HERE = Path(__file__).parent
DEST = HERE/'overnight_upper_two_page_witness_6.json'


def crosses(e, f):
    a, b = sorted(e)
    c, d = sorted(f)
    return (a < c < b < d) or (c < a < d < b)


def coloring(descriptor):
    triangles = [d[0] for d in descriptor]
    for colors in product((0, 1), repeat=len(triangles)):
        if all(colors[i] != colors[j] or
               not any(crosses(e, f) for e in combinations(triangles[i], 2)
                       for f in combinations(triangles[j], 2))
               for i, j in combinations(range(len(triangles)), 2)):
            return colors
    raise AssertionError('The selected triangle factors do not fit two pages.')


def boundary(chain):
    result = defaultdict(Q)
    for (head, edges), coefficient in chain.items():
        for i, edge in enumerate(edges):
            remaining = edges[:i]+edges[i+1:]
            result[(base.addv(head, edge), remaining)] += (-1)**i*coefficient
            result[(head, remaining)] -= (-1)**i*coefficient
    return {k: v for k, v in result.items() if v}


def extract():
    source = HERE/'overnight_upper_triangle_two_pages_6.json'
    data = json.loads(source.read_text())
    selected = [dict(coefficient=c, descriptor=d, page_colors=coloring(d))
                for c, d in zip(data['candidate_coefficients'], data['descriptors']) if c != '0']
    result = dict(status='COMPACT_TWO_PAGE_N6_BOUNDARY_WITNESS', n=6, selected=selected,
                  averaging='Alternating D6 sum, not full S6 averaging.',
                  source_receipt_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  scope='Exact six-label coherent boundary lift. Augmentation correction and filling have not been emitted as a network. No all-N claim.')
    DEST.write_text(json.dumps(result, indent=2)+'\n')
    print('EXTRACTED', len(selected), 'PRODUCT ORBITS', flush=True)


def main():
    start = time.monotonic()
    witness = json.loads(DEST.read_text())
    assert witness['n'] == 6
    base.group = fixed.group
    base.raw_chain = attachment.raw_chain
    chain = defaultdict(Q)
    for selected in witness['selected']:
        descriptor = selected['descriptor']
        assert tuple(selected['page_colors']) == coloring(descriptor)
        coefficient = Q(selected['coefficient'])
        part = base.sym_chain(6, descriptor)
        assert not boundary(part), 'A selected orbit is not a formal cubical cycle.'
        for key, value in part.items():
            chain[key] += coefficient*value
    chain = {k: v for k, v in chain.items() if v}
    assert not boundary(chain)
    expression = base.expression(chain)
    target = base.target(6)
    planes = sorted(set(expression) | set(target))
    representatives = {}
    for plane in planes:
        representatives.setdefault(fixed.plane_orbit(plane), plane)
    gate = base.Verifier(120)
    for plane in representatives.values():
        difference = defaultdict(Q, expression.get(plane, {}))
        for key, value in target.get(plane, {}).items():
            difference[key] -= value
        assert gate.check(difference), ('rational boundary identity', plane)
    augmentation = defaultdict(Q)
    for (_, edges), value in chain.items():
        augmentation[edges] += value
    result = dict(status='EXACT_COMPACT_TWO_PAGE_N6_BOUNDARY_REPLAY', n=6,
                  product_orbits=len(witness['selected']), oriented_products=12*len(witness['selected']),
                  formal_cube_support=len(chain), support_planes=len(planes),
                  plane_orbits_checked=len(representatives),
                  nonzero_augmentation_coefficients=sum(bool(v) for v in augmentation.values()),
                  witness_sha256=hashlib.sha256(DEST.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  seconds=time.monotonic()-start, scope=witness['scope'])
    (HERE/'overnight_upper_two_page_witness_replay_6.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    if '--extract' in sys.argv:
        extract()
    main()
