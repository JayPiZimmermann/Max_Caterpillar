#!/usr/bin/env python3
"""Check every right-kernel relation of the fixed-order N6 product probe."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, time
from flint import nmod_mat
import overnight_upper_triangle_fixed as source
import overnight_upper_triangle_attachments as attachment
import overnight_upper_product_family as base

HERE = Path(__file__).parent


def main():
    start = time.monotonic()
    path = HERE/'overnight_upper_triangle_fixed_6.json'
    data = json.loads(path.read_text())
    width = len(data['descriptors'])
    rr, rank = nmod_mat(data['modular_rows'], data['prime']).rref()
    pivots = [next(j for j in range(width+1) if rr[i, j]) for i in range(rank)]
    assert width in pivots
    free = [j for j in range(width) if j not in pivots]
    base.group = source.group
    base.raw_chain = attachment.raw_chain
    chains = [base.sym_chain(6, descriptor) for descriptor in data['descriptors']]
    verifier = base.Verifier(1000)
    relations, formal = [], 0
    for j in free:
        coefficients = [Q(0)]*width
        coefficients[j] = Q(1)
        for i, p in enumerate(pivots):
            if p < width:
                value = base.ratrec(int(rr[i, j]), data['prime'])
                assert value is not None
                coefficients[p] = -value
        chain = defaultdict(Q)
        for coefficient, column in zip(coefficients, chains):
            if coefficient:
                for key, value in column.items():
                    chain[key] += coefficient*value
        chain = {k: v for k, v in chain.items() if v}
        if not chain:
            formal += 1
        else:
            expression = base.expression(chain)
            representatives = {}
            for plane in expression:
                representatives.setdefault(source.plane_orbit(plane), plane)
            for plane in representatives.values():
                assert verifier.check(expression[plane]), ('failed kernel', j, plane)
        relations.append(list(map(str, coefficients)))
        if len(relations) % 20 == 0:
            print('EXACT KERNELS', len(relations), '/', len(free),
                  'FORMAL', formal, 'SECONDS', time.monotonic()-start, flush=True)
    result = dict(status='EXACT_FIXED_ORDER_TRIANGLE_ATTACHMENT_BOUNDARY_OBSTRUCTION', n=6,
                  source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  ranks=[rank-1, rank], columns=width, relations=relations,
                  free_columns=free, formally_zero_relations=formal,
                  scope=data['scope'], seconds=time.monotonic()-start)
    (HERE/'overnight_upper_triangle_fixed_exact_6.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('DONE', result['status'], result['ranks'], 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
