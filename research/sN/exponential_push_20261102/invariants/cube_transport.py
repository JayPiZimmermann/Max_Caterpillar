"""Exact finite controls for disjoint adjacent-swap transport.

Budget: r=1,2,3, three endpoint slopes, no stochastic search; 60 seconds.
Ranks modulo a fixed prime certify rational rank lower bounds. The matching
upper bounds are the independently derived tensor dimensions in README.md.
Actual quadratic-chain reconstruction is checked separately from endpoint
projection construction. No H(k,q) claim is made by this experiment.
"""
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import time

HERE = Path(__file__).resolve().parent
PRIME = 1000003
VALUES = (-1, 0, 1)
PAIRS = tuple(product(VALUES, repeat=2))
DIAGONAL = tuple(p for p in PAIRS if sum(p) == 0)


def sparse_rank(vectors, prime):
    """Eliminate integer column vectors over F_p; record pivot witnesses."""
    pivots = {}
    witnesses = []
    for index, original in enumerate(vectors):
        vector = {k: v % prime for k, v in original.items() if v % prime}
        while vector:
            key = min(vector)
            if key not in pivots:
                lead = vector[key]
                inv = pow(lead, -1, prime)
                pivots[key] = {k: (v * inv) % prime for k, v in vector.items()}
                witnesses.append((index, key, lead))
                break
            factor = vector[key]
            for k, v in pivots[key].items():
                value = (vector.get(k, 0) - factor * v) % prime
                if value:
                    vector[k] = value
                else:
                    vector.pop(k, None)
    return len(pivots), witnesses


def rational_rank(columns):
    """Independent exact-Q implementation for the one-factor dimension."""
    matrix = [[Fraction(col[i]) for col in columns] for i in range(len(columns[0]))]
    pivot = 0
    for j in range(len(columns)):
        rows = [i for i in range(pivot, len(matrix)) if matrix[i][j]]
        if not rows:
            continue
        i = rows[0]
        matrix[pivot], matrix[i] = matrix[i], matrix[pivot]
        value = matrix[pivot][j]
        matrix[pivot] = [x / value for x in matrix[pivot]]
        for i in range(len(matrix)):
            if i != pivot:
                value = matrix[i][j]
                matrix[i] = [x - value * y for x, y in zip(matrix[i], matrix[pivot])]
        pivot += 1
    return pivot


def actual_chain_check(cell, eta):
    """Construct real quadratic G, then evaluate actual Boolean prefixes.

    Adjacent pair i has endpoints (2i,2i+1); the last vertex is an anchor.
    Endpoint coordinates in `cell` are centered at (eta[i-1]+eta[i])/2.
    """
    r = len(cell)
    beta = []
    delta = []
    old = Fraction(0)
    for (a, b), new in zip(cell, eta):
        center = (old + new) / 2
        beta.extend((center + a - old, center + b - old))
        delta.append(Fraction(-a - b))
        old = new
    beta.append(-old)
    assert sum(beta) + sum(delta) == 0
    assert sum(x != 0 for x in delta) <= r - 1
    for choice in product((0, 1), repeat=r):
        ordering = []
        for i, eps in enumerate(choice):
            ordering.extend((2 * i + eps, 2 * i + 1 - eps))
        ordering.append(2 * r)
        prefix = set()
        for j, vertex in enumerate(ordering):
            prefix.add(vertex)
            actual = sum(beta[i] for i in prefix)
            actual += sum(delta[i] for i in range(r)
                          if 2 * i in prefix and 2 * i + 1 in prefix)
            if j == 2 * r:
                assert actual == 0
            elif j % 2:
                assert actual == eta[j // 2]
            else:
                i = j // 2
                prev = eta[i - 1] if i else Fraction(0)
                assert actual == (prev + eta[i]) / 2 + cell[i][choice[i]]
    return (1 << r) * (2 * r + 1)


def run(r):
    cells = tuple(c for c in product(PAIRS, repeat=r) if any(p in DIAGONAL for p in c))
    index = {c: i for i, c in enumerate(cells)}
    rows = tuple(product(product((0, 1), repeat=r), product(VALUES, repeat=r)))
    row_index = {row: i for i, row in enumerate(rows)}
    columns = []
    for cell in cells:
        columns.append({row_index[(eps, tuple(cell[i][eps[i]] for i in range(r)))]: 1
                        for eps in product((0, 1), repeat=r)})
    actual_rank, pivots = sparse_rank(columns, PRIME)
    target_rank = 5 ** r - 2 ** r
    assert actual_rank == target_rank

    rectangles = []
    for direction in range(r):
        for rest in product(PAIRS, repeat=r - 1):
            if not any(p in DIAGONAL for p in rest):
                continue
            for a in VALUES[1:]:
                for b in VALUES[1:]:
                    rectangle = {}
                    for aa, bb, coefficient in [(-1, -1, 1), (a, -1, -1),
                                               (-1, b, -1), (a, b, 1)]:
                        cell = list(rest)
                        cell.insert(direction, (aa, bb))
                        rectangle[index[tuple(cell)]] = coefficient
                    # Check every literal mixed-crease equality exactly over Z.
                    residual = {}
                    for j, coefficient in rectangle.items():
                        for row, value in columns[j].items():
                            residual[row] = residual.get(row, 0) + coefficient * value
                    assert all(v == 0 for v in residual.values())
                    rectangles.append(rectangle)
    rectangle_rank, rectangle_pivots = sparse_rank(rectangles, PRIME)
    expected_kernel = 9 ** r - 6 ** r - target_rank
    assert rectangle_rank == expected_kernel

    eta = tuple(map(Fraction, (1, -1, 2)[:r]))
    chain_checks = sum(actual_chain_check(c, eta) for c in cells)
    # For r>=2 the common unchanged chain projection itself has both signs.
    if r >= 2:
        assert min(eta) < 0 < max(eta)
    return {
        'swaps': r, 'actual_input_arity': 2 * r + 1,
        'largest_interaction_matching': r - 1,
        'allowed_actual_quadratic_preactivations': len(cells),
        'crease_constraint_rows': len(rows), 'constraint_rank': actual_rank,
        'kernel_dimension': expected_kernel,
        'legal_rectangle_generators': len(rectangles),
        'rectangle_span_rank': rectangle_rank,
        'literal_boolean_prefix_checks': chain_checks,
        'rank_field_prime': PRIME, 'constraint_pivot_certificate': pivots,
        'rectangle_pivot_certificate': rectangle_pivots,
        'all_chambers_mixed_by_common_projection': r >= 2,
    }


started = time.monotonic()
# Independent one-factor exact-Q controls for tensor upper dimensions.
def endpoint_column(pair):
    return tuple(int(v == pair[side]) for side in (0, 1) for v in VALUES)

assert rational_rank([endpoint_column(p) for p in PAIRS]) == 5
assert rational_rank([endpoint_column(p) for p in DIAGONAL]) == 3
assert rational_rank([endpoint_column(p) for p in PAIRS if p not in DIAGONAL]) == 5
results = [run(r) for r in (1, 2, 3)]
# Negative control: genuine matching-two preactivation on seven inputs.
# It is affine after ReLU on every chamber of one complete swap cube,
# while its full Boolean Mobius coefficient is nonzero. An off-cube
# strictly ordered point exhibits its missing mixed crease.
beta = [1, 1, -2, -1, -2, 2, -4]
delta = [(0, 1, 2), (2, 3, 3)]
def control_vertex(mask):
    return sum(beta[i] for i in range(7) if mask >> i & 1) + sum(
        d for a, b, d in delta if mask >> a & 1 and mask >> b & 1)

assert control_vertex(127) == 0
cube_chains = []
for bits in product((0, 1), repeat=3):
    order = []
    for i, bit in enumerate(bits):
        order.extend((2 * i + bit, 2 * i + 1 - bit))
    mask = 0
    chain = []
    for i in order:
        mask |= 1 << i
        chain.append(control_vertex(mask))
    assert min(chain) > 0
    cube_chains.append(chain)
mobius = sum((-1) ** (7 - mask.bit_count()) * max(0, control_vertex(mask))
             for mask in range(128))
assert mobius == 2
off_cube_point = [23, 21, 19, 17, 15, 0, 13]
def control_inner(x):
    return sum(a * b for a, b in zip(beta, x)) + sum(
        d * min(x[a], x[b]) for a, b, d in delta)

assert len(set(off_cube_point)) == 7 and control_inner(off_cube_point) == 0
left, right = off_cube_point.copy(), off_cube_point.copy()
left[6] -= Fraction(1, 10)
right[6] += Fraction(1, 10)
assert control_inner(left) == Fraction(2, 5)
assert control_inner(right) == Fraction(-2, 5)
negative_control = {
    'beta': beta, 'pair_delta': delta, 'all_eight_cube_chains': cube_chains,
    'top_boolean_mobius': mobius, 'off_cube_interior_crease_point': off_cube_point,
    'off_cube_derivative_jump_magnitude': 4,
    'conclusion': 'One cube and its missing-pair interaction condition alone cannot annihilate full Boolean Mobius; compatibility outside that cube is indispensable.',
}
assert time.monotonic() - started < 60
report = {
    'status': 'PASS', 'evidence': 'Exact finite algebra controls; no local-MAX obstruction proved.',
    'results': results, 'negative_control': negative_control,
    'elapsed_seconds': time.monotonic() - started,
    'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'scope': 'All grid endpoint tuples with at least one zero disjoint-pair interaction; complete 2^r chamber cube; all resulting local mixed crease equalities.',
    'conclusion': 'Every cancellation vector in each tested fixed-projection cube is generated by genuine four-unit zero-output rectangles. Mixed cube transport has no further linear obstruction on these families.',
    'not_claimed': 'No statement of H(k,3), full all-real obstruction, or global MAX representability follows from these finite tests.',
}
(HERE / 'cube_transport_result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
for row in results:
    print({k: v for k, v in row.items() if 'certificate' not in k})
