"""Independent structural replay of the local one-root Max4 SMT aggregate.

Does not import the model producer. Arithmetic unsatisfiability is checked
separately by the pinned Ethos CPC replay.
"""
from pathlib import Path
import hashlib
import itertools
import json
import sys

sys.path.insert(0, '/tmp/max5_first11_z3')
import z3

HERE = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def degree(term):
    if z3.is_rational_value(term) or z3.is_int_value(term):
        return 0
    if z3.is_const(term):
        assert term.sort().kind() in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT)
        return 1
    op = term.decl().kind()
    ds = [degree(t) for t in term.children()]
    if op in (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_TO_REAL):
        return max(ds)
    if op == z3.Z3_OP_MUL:
        return sum(ds)
    raise AssertionError(('unexpected operator in local linear equation', term))


def main():
    source = HERE / 'max5_exact_local4_one_root_germs.smt2'
    formulas = z3.parse_smt2_file(str(source))
    assert len(formulas) == 1 and z3.is_or(formulas[0])
    cases = formulas[0].children()
    assert len(cases) == 288
    u, v = z3.Reals('u v')
    bounds = [u > 0, u < 1, v > 0, v < 1]
    points = [(1, 1, 0, 0), (0, 0, -1, 0), (0, 0, 0, -1)]
    assignments = list(itertools.product((0, 2, 3), (1, 2, 3), (0, 1),
                                        [(1, 1), (1, -1), (-1, 1), (-1, -1)],
                                        [(1, 1), (1, -1), (-1, 1), (-1, -1)]))
    assert len(set(assignments)) == 288
    checked = 0
    for branch, (minus_a, minus_b, swap, signs_a, signs_b) in zip(cases, assignments):
        assert z3.is_and(branch) and branch.num_args() == 31
        for i, bound in enumerate(bounds):
            assert z3.eq(z3.simplify(branch.arg(i)), z3.simplify(bound))
        for i in range(4, 28):
            eq = branch.arg(i)
            assert z3.is_eq(eq) and degree(eq.arg(0)) <= 1 and degree(eq.arg(1)) <= 1

        # Rebuild the three point constraints from their physical feature rows.
        positive_a = [i for i in (0, 2, 3) if i != minus_a]
        positive_b = [i for i in (1, 2, 3) if i != minus_b]
        if swap:
            positive_b.reverse()
        normal_a = [z3.RealVal(0) for _ in range(4)]
        normal_b = [z3.RealVal(0) for _ in range(4)]
        normal_a[minus_a] = z3.RealVal(-1)
        normal_a[positive_a[0]], normal_a[positive_a[1]] = u, 1-u
        normal_b[minus_b] = z3.RealVal(-1)
        normal_b[positive_b[0]], normal_b[positive_b[1]] = v, 1-v
        relu = lambda a: z3.If(a >= 0, a, 0)
        for point_index, x in enumerate(points):
            first_a = relu(z3.Sum([a * t for a, t in zip(normal_a, x)]))
            first_b = relu(z3.Sum([b * t for b, t in zip(normal_b, x)]))
            root_feature = max(0, x[0]-x[1])
            values = []
            for row in range(3):
                linear = z3.Sum([z3.Real(f'L{row}_{j}') * x[j] for j in range(4)])
                root_term = z3.Real(f'c{row}') * root_feature
                coeff_a = -signs_a[row] if row < 2 else 1-signs_a.count(-1)
                coeff_b = -signs_b[row] if row < 2 else 1-signs_b.count(-1)
                values.append(linear + root_term + coeff_a*first_a + coeff_b*first_b)
            expected = values[2] + relu(values[0]) + relu(values[1]) - max(x)
            equation = branch.arg(28 + point_index)
            assert z3.is_eq(equation)
            difference = z3.simplify(equation.arg(0)-equation.arg(1)-expected,
                                     som=True, sort_sums=True)
            assert z3.is_rational_value(difference) and difference.as_fraction() == 0
            checked += 1
    ethos = HERE / 'max5_exact_local4_one_root_germs_audit.ethos.json'
    replay = json.loads(ethos.read_text())
    assert replay['status'] == 'INDEPENDENT_ETHOS_PASS'
    assert replay['original_source_sha256'] == sha(source)
    receipt = dict(status='STRUCTURE_AND_INDEPENDENT_ETHOS_PASS', source=source.name,
                   source_sha256=sha(source), disjuncts=288, constraints_per_disjunct=31,
                   strict_ratio_bounds_per_disjunct=4, linear_local_equations_per_disjunct=24,
                   point_conditions_per_disjunct=3, point_conditions_rebuilt=checked,
                   input_points=points, ethos_receipt=ethos.name,
                   ethos_receipt_sha256=sha(ethos), proof_sha256=replay['proof_sha256'],
                   checker_sha256=sha(Path(__file__)),
                   scope='Structural model replay and independent proof replay; geometric necessity audited separately.')
    out = HERE / 'max5_exact_local4_one_root_independent_replay.json'
    out.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
