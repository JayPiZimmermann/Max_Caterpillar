#!/usr/bin/env python3
"""Exact seven-relation upper-rank gate for the N7 exterior-ear test."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, time
from flint import nmod_mat
import overnight_upper_triangle_fixed as fixed
import overnight_upper_triangle_attachments as attachment
import overnight_upper_product_family as base

HERE = Path(__file__).parent


def main():
    start = time.monotonic()
    source = HERE/'overnight_upper_triangle_ear_7.json'
    data = json.loads(source.read_text())
    width = len(data['descriptors'])
    rr, rank = nmod_mat(data['modular_rows'], data['prime']).rref()
    pivots = [next(j for j in range(width+1) if rr[i, j]) for i in range(rank)]
    assert width in pivots
    free = [j for j in range(width) if j not in pivots]
    base.group = fixed.group
    base.raw_chain = attachment.raw_chain
    chains = {}
    verifier = base.Verifier(300)
    relations = []
    for j in free:
        coefficients = [Q(0)]*width
        coefficients[j] = Q(1)
        for i, pivot in enumerate(pivots):
            if pivot < width:
                coefficient = base.ratrec(int(rr[i, j]), data['prime'])
                assert coefficient is not None
                coefficients[pivot] = -coefficient
        chain = defaultdict(Q)
        for index, coefficient in enumerate(coefficients):
            if coefficient:
                if index not in chains:
                    chains[index] = base.sym_chain(7, data['descriptors'][index])
                for key, value in chains[index].items():
                    chain[key] += coefficient*value
        expression = base.expression({k: v for k, v in chain.items() if v})
        representatives = {}
        for plane in expression:
            representatives.setdefault(fixed.plane_orbit(plane), plane)
        for plane in representatives.values():
            assert verifier.check(expression[plane]), ('failed kernel', j, plane)
        relations.append(list(map(str, coefficients)))
        print('EXACT EAR KERNEL', len(relations), '/', len(free), flush=True)
    result = dict(status='EXACT_EXTERIOR_EAR_BOUNDARY_OBSTRUCTION', n=7,
                  ranks=[rank-1, rank], columns=width, free_columns=free,
                  relations=relations, scope=data['scope'],
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  seconds=time.monotonic()-start)
    (HERE/'overnight_upper_triangle_ear_exact_7.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('DONE', result['status'], result['ranks'], 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
