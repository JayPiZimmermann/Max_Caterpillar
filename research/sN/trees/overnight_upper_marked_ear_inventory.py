#!/usr/bin/env python3
"""Share oriented D7 product columns across all marked-edge kernel states."""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import hashlib, json, time
import overnight_upper_oriented_products as oriented
import overnight_upper_marked_kernel_inventory as marked
import overnight_upper_triangle_fixed as fixed
import overnight_upper_product_family as base

HERE = Path(__file__).parent


def descriptor_tuple(d):
    return tuple((tuple(t), r, s) for t, r, s in d)


@lru_cache(None)
def primitive_map(descriptor, character, root, sign):
    ear = ((0, 5, 6), root, sign)
    result = defaultdict(Q)
    image, old_phase = oriented.image_with_phase(descriptor, marked.REFLECTION)
    for d, coefficient in ((descriptor, 1), (image, character*old_phase)):
        target, phase = oriented.canonical(7, d+(ear,))
        if phase:
            result[target] += coefficient*phase
    return {k: v for k, v in result.items() if v}


def main():
    start = time.monotonic()
    witness_path = HERE/'overnight_upper_two_page_witness_6.json'
    witness = json.loads(witness_path.read_text())
    candidates = []
    for sign in (-1, 1):
        expression = defaultdict(Q)
        for item in witness['selected']:
            d = descriptor_tuple(item['descriptor'])
            for pi in fixed.group(6):
                image, old_phase = oriented.image_with_phase(d, pi)
                target, phase = oriented.canonical(7, image+(((0, 5, 6), 0, sign),))
                if phase:
                    expression[target] += Q(item['coefficient'])*base.parity(pi)*old_phase*phase
        candidates.append((dict(kind='particular_lift', character=-1, root=0, sign=sign),
                           {k: v for k, v in expression.items() if v}))
    source_hashes = {}
    for name, character in (('minus', -1), ('plus', 1)):
        path = HERE/f'overnight_upper_marked_kernel_{name}_6.json'
        data = json.loads(path.read_text())
        assert data['status'] == 'EXACT_MARKED_EDGE_CONING_KERNEL_SPACE'
        source_hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
        descriptors = [descriptor_tuple(d) for d in data['descriptors']]
        roots = (0,) if character == -1 else (0, 6)
        for state_index, (relation, support) in enumerate(zip(data['relations_sparse'], data['formal_cube_supports'])):
            if not support:
                continue
            for root in roots:
                for sign in (-1, 1):
                    expression = defaultdict(Q)
                    for index, coefficient in relation:
                        for target, value in primitive_map(descriptors[index], character, root, sign).items():
                            expression[target] += Q(coefficient)*value
                    candidates.append((dict(kind='kernel', character=character,
                                            state=state_index, root=root, sign=sign),
                                       {k: v for k, v in expression.items() if v}))
        # The discarded ear choices are exact consequences of H covariance.
        for d in descriptors[:10]:
            for sign in (-1, 1):
                left = primitive_map(d, character, 0, sign)
                right = primitive_map(d, character, 5, sign)
                assert right == {k: -character*v for k, v in left.items()}
                if character == -1:
                    assert not primitive_map(d, character, 6, sign)
    distinct, seen, quotient = [], {}, []
    for label, expression in candidates:
        if not expression:
            quotient.append(dict(source=label, column=None))
            continue
        scale = expression[min(expression)]
        signature = tuple(sorted((k, v/scale) for k, v in expression.items()))
        if signature not in seen:
            seen[signature] = len(distinct)
            distinct.append((label, expression))
        column = seen[signature]
        reference = distinct[column][1]
        quotient.append(dict(source=label, column=column, scale=str(scale/reference[min(reference)])))
    primitives = sorted({p for _, expression in distinct for p in expression})
    index = {p: i for i, p in enumerate(primitives)}
    columns = [dict(label=label, coefficients=[[index[p], str(c)] for p, c in sorted(expression.items())])
               for label, expression in distinct]
    result = dict(status='COMPLETE_MARKED_AFFINE_EAR_IMAGE_INVENTORY', n=7,
                  primitive_descriptors=primitives, columns=columns, source_quotient=quotient,
                  source_hashes=source_hashes,
                  witness_sha256=hashlib.sha256(witness_path.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='The particular N6 lift plus the complete kernels in both marked-edge reflection sectors, multiplied by all ear attachment/reflection states and D7 averaged. Ear choices are reduced by exact stabilizer covariance, with every source state recorded in the quotient map.',
                  seconds=time.monotonic()-start)
    (HERE/'overnight_upper_marked_ear_inventory_7.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('MARKED EAR INVENTORY', len(candidates), 'SOURCE STATES', len(columns),
          'DISTINCT COLUMNS', len(primitives), 'SHARED PRODUCT ORBITS',
          'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
