#!/usr/bin/env python3
"""A smallest exact test of multiplying a coning-kernel crossing relation."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, random
import overnight_upper_triangle_attachments as attachment
import overnight_upper_product_family as base
from overnight_upper_triangle_attachment_exact import evaluate

HERE = Path(__file__).parent


def relation(n, extra=False):
    descriptors = [(((0, 1, 2), 0, 1), ((0, 3, 4), 0, -1)),
                   (((0, 1, 3), 0, 1), ((0, 2, 4), 0, -1))]
    if extra:
        descriptors = [d + (((0, 4, 5), 0, 1),) for d in descriptors]
    out = defaultdict(Q)
    for descriptor in descriptors:
        for key, coefficient in attachment.raw_chain(n, descriptor).items():
            out[key] += coefficient
    return {key: value for key, value in out.items() if value}


def main():
    smaller = base.expression(relation(5))
    verifier = base.Verifier(30)
    for plane, expression in smaller.items():
        assert verifier.check(expression), ('five-label kernel premise', plane)
    larger = base.expression(relation(6, True))
    rng = random.Random(251033)
    witness = None
    for plane, expression in sorted(larger.items()):
        for _ in range(10):
            point = tuple(rng.randrange(1, 20) for _ in range(4))
            try:
                value = evaluate(expression, point)
            except ZeroDivisionError:
                continue
            if value:
                witness = dict(plane=plane, point=point, value=str(value),
                               terms=[dict(numerator=num, power=power,
                                           denominator=den, coefficient=str(coefficient))
                                      for (num, power, den), coefficient in expression.items()])
                break
        if witness:
            break
    assert witness, 'No counterexample found; this is not an exact zero test.'
    result = dict(status='EXACT_CONING_KERNEL_NOT_CLOSED_UNDER_CYCLE_PRODUCT',
                  premise='rho(Gamma_012^+ Gamma_034^- + Gamma_013^+ Gamma_024^-)=0 on five labels, all triangles attached at 0.',
                  multiplier='Gamma_045^+ on the six-label space, attached at 0.',
                  conclusion='The coned class of the multiplied cycle is nonzero.',
                  witness=witness, premise_planes_checked=len(smaller),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Refutes multiplication of this specific exact crossing relation in the coning quotient. It does not exclude recurrences retaining additional boundary corrections.')
    (HERE/'overnight_upper_product_congruence.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], witness['plane'], witness['point'], witness['value'], flush=True)


if __name__ == '__main__':
    main()
