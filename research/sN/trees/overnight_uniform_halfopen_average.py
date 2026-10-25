#!/usr/bin/env python3
"""One bounded covariant-boundary correction, not a jet search."""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib
import json
import time
from overnight_uniform_halfopen_verify import constant, direct_star_terms, vertex


def main():
    started = time.monotonic()
    representative = (0, 1, 10, 100, 1000)
    terms = direct_star_terms()
    target_basis = tuple(vertex(i) for i in range(1, 5))
    rows = []
    total = target_total = Q(0)
    for p in permutations(representative):
        eta = tuple(x - p[0] for x in p[1:])
        value = sum(coefficient * constant(basis, eta)
                    for basis, coefficient in terms.items())
        target = constant(target_basis, eta)
        total += value
        target_total += target
        rows.append(dict(eta=eta, star_value=str(value), target_value=str(target)))
    assert target_total / 120 == Q(1, 80)
    result = dict(status='EXACT_N5_LABEL_AVERAGED_HALFOPEN_CONSTANT_GATE',
                  eta_orbit_representative=representative,
                  star_full_orbit_average=str(total / 120),
                  maximum_average=str(target_total / 120),
                  annihilates_outward_star=(total == 0),
                  rows=rows, seconds=time.monotonic() - started,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Only the scalar constant coefficient at the declared parity torsion curve, with a common boundary vector averaged over labels.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}, indent=2))


if __name__ == '__main__':
    main()
