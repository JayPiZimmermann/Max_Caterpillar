#!/usr/bin/env python3
"""Exact falsification test for a paired-frequency degeneration functional.

At odd arity m=2q+1, let frequencies tend to (0,+z1,-z1,...),
with direction (m-1,-1,...,-1), preserving their zero sum. Test the
t^(-1) coefficient of the full symmetric orbit kernel. A nonzero value
for a tree without a perfect matching refutes this proposed separator.
This tests one functional, not the general separation conjecture.
Budget: 120 seconds. Uses rational arithmetic throughout.
"""
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

import networkx as nx
from dfs_review_fourier import family


def coeff_minus_one(unit, base, slope):
    m = len(base)
    a0, a1 = base[0], slope[0]
    zeros = []
    nonzeros = []
    for side, sign in unit['cuts']:
        q0 = sum(base[i] for i in side)
        q1 = sum(slope[i] for i in side)
        for c, d in ((q0, q1), (q0+sign*a0, q1+sign*a1)):
            if c == 0:
                assert d != 0, 'Path lies on a pole'
                zeros.append(d)
            else:
                nonzeros.append((c, d))
    p = len(zeros)
    if p == 0:
        return Fraction(0)
    degree = m-4
    series = [Fraction(math.comb(degree, j)*(-a0)**(degree-j)*(-a1)**j)
              if j <= degree else Fraction(0) for j in range(p)]
    for c, d in nonzeros:
        inv = [Fraction((-d)**j, c**(j+1)) for j in range(p)]
        series = [sum(series[k]*inv[j-k] for k in range(j+1))
                  for j in range(p)]
    return series[p-1] / math.prod(zeros)


def main(m):
    assert m >= 5 and m % 2 == 1
    start = time.monotonic()
    q = (m-1)//2
    base = [0] + [s*10**i for i in range(q) for s in (1, -1)]
    slope = [m-1] + [-1]*(m-1)
    perms = list(itertools.permutations(range(m)))
    units = [u for u in family(m, 'all')
             if len(nx.max_weight_matching(nx.Graph(u['edges']), maxcardinality=True)) < q]
    checked = []
    for idx, unit in enumerate(units):
        assert time.monotonic()-start < 120
        value = sum(coeff_minus_one(unit, [base[i] for i in p], [slope[i] for i in p])
                    for p in perms)
        checked.append(dict(index=idx, value=str(value)))
        if value:
            break
    target = Fraction((-1)**(m-1), (m-1)*math.prod(base[1:]))
    result = dict(arity=m, base=base, slope=slope, family_columns=len(units),
                  checked=checked, target=str(target),
                  status='PAIRED_LIMIT_SEPARATOR_REFUTED' if checked[-1]['value'] != '0'
                         else 'NO_COUNTEREXAMPLE_IN_COMPLETE_FINITE_FAMILY',
                  witness=units[checked[-1]['index']],
                  budget_seconds=120, elapsed_seconds=time.monotonic()-start,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Only this coefficient functional at this arity; no uniform claim')
    out = Path(__file__).with_name(f'overnight_lower_pairlimit_{m}.json')
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
