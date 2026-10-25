#!/usr/bin/env python3
"""Exact local controls for the faithful multiplicative tree-kernel formula."""
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import time
import sympy as S


def main():
    started = time.monotonic()
    lattice_rows = []
    for d in range(5):
        configurations = 0
        for values in product(range(-2, 3), repeat=d + 1):
            t, leaves = values[0], values[1:]
            left = 0
            for bits in product((0, 1), repeat=d):
                shift = sum(max(0, x + b) for x, b in zip(leaves, bits))
                for j, coefficient in enumerate((1, -2, 1)):
                    left += (-1) ** (d - sum(bits)) * coefficient * max(0, t + j + shift)
            right = 0
            if all(x >= 0 for x in leaves):
                right = sum((-1) ** (d + 2 - j) * math.comb(d + 2, j)
                            * max(0, t + sum(leaves) + j) for j in range(d + 3))
            assert left == right, (d, values, left, right)
            configurations += 1
        lattice_rows.append(dict(inner_variables=d, lattice_points=configurations,
                                 mixed_forward_difference_identity=True))

    A, X, Y, d, negative = S.symbols('A X Y d negative')
    plus = lambda q: q / ((1 - q) * (1 - A * q))
    minus = lambda q: q / ((1 - q) * (A - q))
    fay = (plus(X) * minus(Y) - minus(X) * plus(Y)
           - plus(X * Y) * plus(X) + plus(X * Y) * plus(Y)
           + minus(X * Y) * minus(X) - minus(X * Y) * minus(Y))
    assert S.cancel(fay) == 0
    assert S.cancel((1-X)/(1-A*X) + (1-A)*X/(1-A*X) - 1) == 0
    assert S.cancel((1-X)/(A-X) - (1-A)*X/(A*(A-X)) - 1/A) == 0
    assembly = -1/A + (1/A-1)*(1-negative) - (d-2) + (d-negative) + negative/A
    assert S.expand(assembly - 1) == 0

    # Two labels and one edge give independent target normalization controls.
    z, w = S.symbols('z w')
    assert S.cancel(-1/((1-z)*(1-1/z)) - z/(1-z)**2) == 0
    apex = 1/(z*w)
    edge = w
    max3_tree = -apex*edge/(1-apex)/((1-edge)*(1-apex*edge))
    assert S.cancel(max3_tree - 1/((1-apex)*(1-z)*(1-w))) == 0
    result = dict(status='EXACT_MULTIPLICATIVE_KERNEL_LOCAL_CONTROLS',
                  lattice_rows=lattice_rows,
                  multiplicative_six_term_fay_identity=True,
                  uniform_logarithmic_derivative_assembly=True,
                  max2_and_max3_normalizations=True,
                  seconds=time.monotonic()-started,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Finite and symbolic controls of the uniform proof in the companion note. No outward-twin separator or exponential lower bound is established.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
