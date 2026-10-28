#!/usr/bin/env python3
"""Exact coning-kernel state space of the complete N6 two-page subfamily."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, time
from flint import nmod_mat
import overnight_upper_triangle_attachments as attachment
import overnight_upper_triangle_fixed as fixed
import overnight_upper_product_family as base

HERE = Path(__file__).parent


def build_states(data):
    base.raw_chain = attachment.raw_chain
    base.group = fixed.group
    primitives = [base.sym_chain(6, descriptor) for descriptor in data['descriptors']]
    result = []
    for state in data['states']:
        chain = defaultdict(Q)
        for index, coefficient in state['coefficients']:
            for key, value in primitives[index].items():
                chain[key] += Q(coefficient)*value
        result.append({k: v for k, v in chain.items() if v})
    return result


def main():
    start = time.monotonic()
    source = HERE/'overnight_upper_triangle_two_pages_6.json'
    data = json.loads(source.read_text())
    width = len(data['descriptors'])
    rr, rank = nmod_mat(data['modular_rows'], data['prime']).rref()
    pivots = [next(j for j in range(width+1) if rr[i, j]) for i in range(rank)]
    assert width not in pivots
    free = [j for j in range(width) if j not in pivots]
    states = [dict(kind='particular_lift', coefficients=[[i, c] for i, c in enumerate(data['candidate_coefficients']) if c != '0'])]
    for j in free:
        coefficients = {j: Q(1)}
        for i, pivot in enumerate(pivots):
            coefficient = base.ratrec(int(rr[i, j]), data['prime'])
            assert coefficient is not None
            if coefficient:
                coefficients[pivot] = -coefficient
        states.append(dict(kind='coning_kernel', free_column=j,
                           coefficients=[[i, str(c)] for i, c in sorted(coefficients.items())]))
    result = dict(status='PROPOSED_TWO_PAGE_CONING_KERNEL_STATES', n=6,
                  descriptors=data['descriptors'], states=states,
                  ordinary_rank=rank, kernel_dimension=len(free),
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Complete coning-kernel basis of the 166 D6-averaged columns in the N6 two-page subfamily, together with its fixed exact particular lift. This is not the full unsymmetrized kernel.')
    chains = build_states(result)
    verifier = base.Verifier(300)
    target = base.target(6)
    for index, chain in enumerate(chains):
        expression = base.expression(chain)
        if not index:
            for plane, terms in target.items():
                expression.setdefault(plane, {})
                for key, value in terms.items():
                    expression[plane][key] = expression[plane].get(key, Q(0))-value
        representatives = {}
        for plane in expression:
            representatives.setdefault(fixed.plane_orbit(plane), plane)
        for plane in representatives.values():
            assert verifier.check(expression[plane]), ('state identity', index, plane)
        result['states'][index]['formal_cube_support'] = len(chain)
    result['status'] = 'EXACT_TWO_PAGE_CONING_KERNEL_STATE_SPACE'
    result['seconds'] = time.monotonic()-start
    (HERE/'overnight_upper_boundary_kernel_states_6.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print(result['status'], 'RANK', rank, 'KERNEL', len(free),
          'FORMALLY NONZERO', sum(bool(c) for c in chains[1:]),
          'MAX SUPPORT', max(map(len, chains)), 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
