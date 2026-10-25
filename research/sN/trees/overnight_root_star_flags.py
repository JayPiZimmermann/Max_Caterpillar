#!/usr/bin/env python3
"""Necessary control for extending the canonical-star flag separator.

This evaluates actual vertex sets.  A nonzero star value refutes this specific
extension; zero values on the finite controls are not a continuous-family proof.
"""
from fractions import Fraction
from itertools import combinations_with_replacement, permutations, product
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
FLAGS = json.loads((HERE / 'dfs_review_flag_certificate.log').read_text())['flags']
PERMS = list(permutations(range(5)))


def flag_value(vertices, directions, coordinate):
    if not directions:
        vals = [v[coordinate] for v in vertices]
        return max(vals) - min(vals)
    u, *tail = directions
    vals = [sum(a*b for a, b in zip(v, u)) for v in vertices]
    lo, hi = min(vals), max(vals)
    if lo == hi:
        return 0
    return (flag_value([v for v, t in zip(vertices, vals) if t == hi], tail, coordinate)
            - flag_value([v for v, t in zip(vertices, vals) if t == lo], tail, coordinate))


SYMMETRIC_FLAGS = []
for p in PERMS:
    inv = [p.index(i) for i in range(5)]
    for flag in FLAGS:
        dirs = [tuple(u[inv[i]] for i in range(5)) for u in flag['directions']]
        SYMMETRIC_FLAGS.append((dirs, p[flag['final_coordinate']], Fraction(flag['weight'])))


def value(vertices):
    return sum(w*flag_value(vertices, dirs, j) for dirs, j, w in SYMMETRIC_FLAGS)


def star(head, weights):
    # Apex coordinate 0; star centre 1; leaves 2,3,4.
    h = [-1, 1-sum(head), *head]
    vertices = {(0,)*5}
    for bits in product((0, 1), repeat=3):
        v = h.copy()
        for i, (b, w) in enumerate(zip(bits, weights), 2):
            v[1] -= b*w
            v[i] += b*w
        vertices.add(tuple(v))
    return sorted(vertices)


def main():
    start = time.monotonic()
    target = value([tuple(int(i == j) for i in range(5)) for j in range(5)])
    assert target == 120
    canonical = 0
    for root in range(4):
        for backwards in product((0, 1), repeat=3):
            head = [int(root == i+1)-backwards[i] for i in range(3)]
            assert value(star(head, (1, 1, 1))) == 0, (root, backwards)
            canonical += 1
    tested = 0
    examples = []
    for weights in [(1, 1, 1), (1, 1, 2), (1, 2, 3)]:
        heads = (combinations_with_replacement(range(-3, 4), 3) if len(set(weights)) == 1
                 else product(range(-2, 3), repeat=3))
        for head in heads:
            z = value(star(head, weights))
            tested += 1
            if z:
                examples.append(dict(head=head, weights=weights, value=str(z)))
                break
    result = dict(status='SPECIFIC_EXTENSION_REFUTED' if examples else 'FINITE_CONTROLS_ONLY',
                  target=str(target), canonical_oriented_controls=canonical,
                  tested=tested, counterexamples=examples,
                  seconds=round(time.monotonic()-start, 3))
    (HERE/'overnight_root_star_flags.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
