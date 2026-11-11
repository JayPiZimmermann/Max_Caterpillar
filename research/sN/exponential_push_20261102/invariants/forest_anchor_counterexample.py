"""Exact all-input-arity-family controls for the forest-to-C_r span shortcut.

The proof is in README.md. These integer tests recompute actual quadratic
Boolean functions, actual gradients on complete adjacent-swap cubes, and
primitive anchor/cover conditions independently of the proposed invariant.
No random sampling, optimization, floating-point arithmetic, or MAX claim.
"""
from itertools import combinations, product
from fractions import Fraction
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent


def quadratic(beta, delta, subset):
    return sum(beta[i] for i in subset) + sum(
        value for (a, b), value in delta.items() if a in subset and b in subset)


def gradient(beta, delta, ordering):
    """Actual Lovasz gradient from Boolean prefix increments."""
    subset = set()
    old = 0
    out = [0] * len(beta)
    for label in ordering:
        subset.add(label)
        new = quadratic(beta, delta, subset)
        out[label] = new - old
        old = new
    assert old == 0
    return tuple(out)


def cube_order(r, bits):
    out = []
    for i, bit in enumerate(bits):
        out.extend((2 * i + bit, 2 * i + 1 - bit))
    return tuple(out + [2 * r, 2 * r + 1])


def coefficient(normal, v):
    # Normalize the full-support hyperplane by its last coefficient v_z=1.
    scale = normal[-1]
    return abs(scale) if scale and all(a == scale * b for a, b in zip(normal, v)) else 0


def anchored_quadratic(n, anchor):
    if not anchor:
        return [0] * n, {}
    delta = {(a, b): ((a + 2) * (b + 3) % 7) - 3
             for a, b in combinations(range(n), 2) if a in anchor or b in anchor}
    beta = [0] * n
    for i in range(n):
        if i in anchor:
            beta[i] = i + 1
        else:
            beta[i] = -sum(delta.get(tuple(sorted((i, a))), 0) for a in anchor)
    beta[min(anchor)] -= quadratic(beta, delta, anchor)
    for bits in range(1 << n):
        subset = {i for i in range(n) if bits >> i & 1}
        if anchor <= subset:
            assert quadratic(beta, delta, subset) == 0
    return beta, delta


def cover_quadratic(n, cover):
    delta = {(a, b): ((a + 3) * (b + 2) % 9) - 4
             for a, b in combinations(range(n), 2) if a in cover or b in cover}
    beta = [i - 2 for i in range(n)]
    beta[-1] -= sum(beta) + sum(delta.values())
    return beta, delta


def invariant(beta, delta, r, v):
    pattern = []
    for bits in product((0, 1), repeat=r):
        pattern.append(coefficient(gradient(beta, delta, cube_order(r, bits)), v))
    charge = sum((-1) ** sum(bits) * c
                 for bits, c in zip(product((0, 1), repeat=r), pattern))
    return pattern, charge


def determinant(matrix):
    a = [[Fraction(x) for x in row] for row in matrix]
    answer = Fraction(1)
    for i in range(len(a)):
        pivot = next(j for j in range(i, len(a)) if a[j][i])
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            answer = -answer
        lead = a[i][i]
        answer *= lead
        for j in range(i + 1, len(a)):
            scale = a[j][i] / lead
            a[j] = [x - scale * y for x, y in zip(a[j], a[i])]
    assert answer.denominator == 1
    return int(answer)


def run(r):
    n = 2 * r + 2
    v = [1] * (2 * r) + [-(2 * r + 1), 1]
    # First the pair edges, then additional comparisons that vanish on
    # every chamber of the entire cube. Together they form a spanning
    # tree of cover r, so this counterexample survives ridge-rank pruning.
    comparisons = [(2 * i + 1, 2 * i) for i in range(r)]
    comparisons += [(2 * i + 2, 2 * i) for i in range(r - 1)]
    comparisons += [(2 * r, 0), (2 * r + 1, 0)]
    beta = v.copy()
    delta = {}
    for pos, neg in comparisons:
        beta[pos] += 1
        pair = tuple(sorted((pos, neg)))
        assert pair not in delta
        delta[pair] = -1
    assert len(delta) == n - 1
    cover = set(range(0, 2 * r, 2))
    assert all(a in cover or b in cover for a, b in delta)
    incidence = [[int(i == pos) - int(i == neg) for i in range(n - 1)]
                 for pos, neg in comparisons]
    basis_determinant = determinant(incidence)
    assert abs(basis_determinant) == 1
    assert sum(beta) + sum(delta.values()) == 0
    pattern, charge = invariant(beta, delta, r, v)
    assert pattern == [1] + [0] * ((1 << r) - 1)
    assert charge == 1

    samples = []
    t = r * (2 * r + 1)
    for bits in product((0, 1), repeat=r):
        order = cube_order(r, bits)
        point = [0] * n
        for j in range(2 * r + 1):
            point[order[j]] = t + 2 * r - j
        assert all(point[order[j]] > point[order[j + 1]] for j in range(n - 1))
        assert sum(a * b for a, b in zip(v, point)) == 0
        actual_g = sum(a * b for a, b in zip(v, point))
        actual_g += sum(max(0, point[pos] - point[neg]) for pos, neg in comparisons)
        assert actual_g == sum(bits)
        samples.append({'bits': bits, 'point': point, 'g': actual_g})

    # Genuine nonzero anchor-one and modular controls: both supply crease
    # coefficient1 in every chamber, giving zero alternating charge.
    assert invariant(v, {}, r, v) == ([1] * (1 << r), 0)
    a_beta = v.copy()
    a_beta[-1] = 0
    a_delta = {(i, n - 1): -v[i] for i in range(n - 1)}
    assert invariant(a_beta, a_delta, r, v) == ([1] * (1 << r), 0)

    checks = 0
    if r <= 3:
        for a in range(r + 1):
            for A_tuple in combinations(range(n), a):
                A = set(A_tuple)
                b, d = anchored_quadratic(n, A)
                if n - 1 not in A:
                    for bits in product((0, 1), repeat=r):
                        assert gradient(b, d, cube_order(r, bits))[-1] == 0
                else:
                    missing = next(i for i in range(r)
                                   if 2 * i not in A and 2 * i + 1 not in A)
                    assert d.get((2 * missing, 2 * missing + 1), 0) == 0
                    for bits in product((0, 1), repeat=r):
                        flipped = list(bits)
                        flipped[missing] ^= 1
                        assert gradient(b, d, cube_order(r, bits)) == gradient(b, d, cube_order(r, flipped))
                assert invariant(b, d, r, v)[1] == 0
                checks += 1
        for a in range(r):
            for A_tuple in combinations(range(n), a):
                A = set(A_tuple)
                b, d = cover_quadratic(n, A)
                missing = next(i for i in range(r)
                               if 2 * i not in A and 2 * i + 1 not in A)
                assert d.get((2 * missing, 2 * missing + 1), 0) == 0
                assert invariant(b, d, r, v)[1] == 0
                checks += 1
    return {'r': r, 'n': n, 'v': v, 'actual_boolean_beta': beta,
            'actual_boolean_delta': [[*pair, value] for pair, value in delta.items()],
            'original_comparison_rows': comparisons,
            'translation_quotient_basis_determinant': basis_determinant,
            'interaction_graph': 'Spanning tree with cover and matching number exactly r',
            'target_crease_pattern': pattern, 'target_cube_charge': charge,
            'exact_Hv_samples': samples, 'primitive_Cr_controls': checks}


report = {'status': 'PASS', 'evidence': 'Exact integer controls plus general all-real proof in README.md; not a Lean-verified span theorem.',
          'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'results': [run(r) for r in range(1, 6)],
          'refuted_claim': 'Each ReLU of a quadratic braid preactivation with forest interaction graph of vertex cover r lies in the finite signed span of anchor<=r units, vertex-cover<=r-1 units, and shallow braid functions.',
          'scope_limit': 'Unitwise span reduction is false. A cancellation-sensitive reduction of an entire already-glued network is not refuted.'}
(HERE / 'forest_anchor_counterexample_result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'],
                  'results': [{'r': x['r'], 'n': x['n'], 'charge': x['target_cube_charge'],
                               'primitive_Cr_controls': x['primitive_Cr_controls']} for x in report['results']]}, indent=2))
