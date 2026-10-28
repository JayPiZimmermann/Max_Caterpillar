#!/usr/bin/env python3
"""Independent rational Laurent control of the repeated-frequency engine.

Uses all 120 permutations and root-away cuts directly, not the subset DAG
or its polynomial evaluator. Checks every five-label star orbit at three
parameters, including exact cancellation of all negative Laurent powers.
"""
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import struct
import time

HERE = Path(__file__).resolve().parent
PRIME = 1000003


def coefficient(unit, base, slope, order):
    m = len(base)
    zero = []
    regular = []
    for side, sign in unit['cuts']:
        c = sum(base[i] for i in side)
        d = sum(slope[i] for i in side)
        for left, right in ((c, d), (c+sign*base[0], d+sign*slope[0])):
            if left:
                regular.append((left, right))
            else:
                assert right
                zero.append(right)
    wanted = len(zero)+order
    if wanted < 0:
        return Fraction(0)
    exponent = m-4
    series = [Fraction(math.comb(exponent, j)*(-base[0])**(exponent-j)*(-slope[0])**j)
              if j <= exponent else Fraction(0) for j in range(wanted+1)]
    for c, d in regular:
        inverse = [Fraction((-d)**j, c**(j+1)) for j in range(wanted+1)]
        series = [sum(series[k]*inverse[j-k] for k in range(j+1))
                  for j in range(wanted+1)]
    return series[wanted]/math.prod(zero)


def main():
    started = time.monotonic()
    domain = json.loads((HERE/'overnight_lower_coalescence_5_domain.json').read_text())
    units = domain['representatives']
    assert len(units) == 10
    matrix_path = HERE/'overnight_lower_coalescence_5.u32'
    flat = struct.unpack('<'+'I'*(matrix_path.stat().st_size//4), matrix_path.read_bytes())
    permutations = list(itertools.permutations(range(5)))
    records = []
    for x in (20, 21, 47):
        base = [-x-3, 1, 1, 1, x]
        slope = [-6, 1, 2, 3, 0]
        expected = flat[(x-20)*11:(x-19)*11]
        exact = []
        for unit in units:
            values = [Fraction(0)]*4
            for pi in permutations:
                b, s = [base[i] for i in pi], [slope[i] for i in pi]
                for j, order in enumerate(range(-3, 1)):
                    values[j] += coefficient(unit, b, s, order)
            assert values[:3] == [0, 0, 0]
            exact.append(values[-1])
        exact.append(Fraction(1, math.prod(base)))
        reduced = [v.numerator*pow(v.denominator, -1, PRIME)%PRIME for v in exact]
        assert reduced == list(expected)
        records.append(dict(x=x, exact_values=list(map(str, exact)), all_poles_cancel=True))
    result = dict(status='INDEPENDENT_EXACT_LAURENT_CONTROLS_PASS', arity=5,
                  orbit_columns=10, points=3, permutations_per_orbit=120,
                  exact_rows=records, seconds=time.monotonic()-started,
                  budget_seconds=120, matrix_sha256=hashlib.sha256(matrix_path.read_bytes()).hexdigest(),
                  evaluator_source_sha256=hashlib.sha256((HERE/'overnight_lower_coalescence.cpp').read_bytes()).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Finite evaluator controls, not a new lower-bound theorem')
    (HERE/'overnight_lower_coalescence_check.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
