"""Necessary exact-three-shared-contact Max5 models.

The general mode permits arbitrary additional invariant rows, including
extra roots and opposite/proportional rows. Curvatures are consolidated
before local-germ comparisons; actual linear parts are retained.
SAT is only necessary data. No finite test claims global identification.
"""
import argparse
import json
import sys
import time
from itertools import combinations, product
from pathlib import Path

sys.path.insert(0, '/tmp/max5_first11_z3')
import z3 as z


def build(kind, mode='general', samples='boolean', shared_germs=False,
          wall=True, timeout=60000, rigid=False, supports=None, coefficient_gauge=False):
    # Each tuple is (contact, owner, positive pair, negative pair).
    if kind == 'one_each_same':
        contacts = [(0, 0, (3, 4), (1, 2)),
                    (1, 1, (3, 4), (0, 2))]
    elif kind == 'one_each_path':
        contacts = [(0, 0, (3, 4), (1, 2)),
                    (1, 1, (2, 4), (0, 3))]
    elif kind == 'two_one_core':
        contacts = [(0, 0, (3, 4), (1, 2)),
                    (1, 0, (3, 4), (0, 2))]
    else:
        raise ValueError(kind)
    edges = sorted({e for _, _, p, n in contacts for e in (p, n)})
    m = len(edges)
    extra_supports = None
    if supports is not None:
        extra_supports = sorted(tuple(sorted(s)) for s in supports)
        assert len(extra_supports) == 7
        for edge in edges:
            extra_supports.remove(edge)
    orient = [z.Bool('orient%d' % j) for j in range(m)]
    rows = [[z.If(orient[j], int(k == a)-int(k == b),
                  int(k == b)-int(k == a)) for k in range(5)]
            for j, (a, b) in enumerate(edges)]
    rows += [[z.Real('a%d_%d' % (j, k))
              if extra_supports is None or k in extra_supports[j-m] else z.RealVal(0)
              for k in range(5)]
             for j in range(m, 7)]
    cores = [[z.Real('%s%d' % (name, j)) for j in range(7)]
             for name in ('g', 'h')]
    remainder = [z.Real('r%d' % j) for j in range(7)]
    ell = [z.Real('e%d' % k) for k in range(5)]
    active = [z.Bool('active%d' % i) for i in range(2)]
    solver = z.SolverFor('QF_NRA')
    solver.set(timeout=timeout)
    solver.add(sum(ell) == 1)
    absz = lambda t: z.If(t >= 0, t, -t)
    relu = lambda t: z.If(t > 0, t, 0)
    dot = lambda a, b: sum(u*v for u, v in zip(a, b))
    known_supports = edges + extra_supports if extra_supports is not None else None
    norm = [z.RealVal(2) if j < m or (known_supports is not None and len(known_supports[j]) == 2)
            else sum(absz(t) for t in a) for j, a in enumerate(rows)]
    parallel = [[z.BoolVal(j == k) if j == k or
                    (known_supports is not None and known_supports[j] != known_supports[k])
                 else z.BoolVal(True) if known_supports is not None and len(known_supports[j]) == 2
                 else z.And(*[rows[j][a]*rows[k][b] == rows[j][b]*rows[k][a]
                              for a, b in combinations(range(5), 2)])
                 for k in range(7)] for j in range(7)]
    for j in range(m, 7):
        a = rows[j]
        solver.add(sum(a) == 0)
        if extra_supports is not None:
            solver.add(*[a[k] != 0 for k in extra_supports[j-m]])
        # Positive scaling fixes the first nonzero row coordinate to +/-1.
        # This gauge does not normalize or omit any core/remainder coefficient.
        if coefficient_gauge and (known_supports is None or len(known_supports[j]) > 2):
            g, h, r = cores[0][j], cores[1][j], remainder[j]
            solver.add(z.Or(g == 1, g == -1,
                           z.And(g == 0, z.Or(h == 1, h == -1)),
                           z.And(g == 0, h == 0, z.Or(r == 1, r == -1))))
            solver.add(z.Or(*[t != 0 for t in a]))
        else:
            solver.add(z.Or(*[z.And(*[a[t] == 0 for t in range(k)],
                                         z.Or(a[k] == 1, a[k] == -1))
                                  for k in range(5)]))
        if mode == 'distinct_nonroot':
            solver.add(z.Sum(*[z.If(t != 0, 1, 0) for t in a]) >= 3)
    if mode == 'distinct_nonroot':
        for j, k in combinations(range(m, 7), 2):
            solver.add(z.Not(parallel[j][k]))

    def curvature(coeff, j):
        # On a fixed hyperplane, every normal has the same direction up to
        # sign. L1 length is therefore the correct positive scale factor.
        return sum(z.If(parallel[j][k], coeff[k]*norm[k], 0)
                   for k in range(7))

    def midpoint_gradient(coeff, i, k):
        return sum(coeff[j]*z.If(rows[j][i] < 0, rows[j][k],
                                 z.If(rows[j][i] == 0, z.RealVal('1/2')*rows[j][k], 0))
                   for j in range(7))

    def value(coeff, i):
        return sum(coeff[j]*relu(-rows[j][i]) for j in range(7))

    def root_parallel(j, edge):
        # A nonzero zero-sum row is parallel to e_a-e_b exactly when its
        # other coordinates vanish.
        if known_supports is not None:
            return z.BoolVal(known_supports[j] == tuple(sorted(edge)))
        return z.And(*[rows[j][k] == 0 for k in range(5) if k not in edge])

    for i, owner, pos, neg in contacts:
        own, other = cores[owner], cores[1-owner]
        effective = [remainder[j] + z.If(active[i], other[j], 0)
                     for j in range(7)]
        for j in range(7):
            solver.add(z.Implies(rows[j][i] == 0,
                       curvature(own, j) ==
                       2*z.If(root_parallel(j, pos), 1, 0)
                       - 2*z.If(root_parallel(j, neg), 1, 0)))
            solver.add(z.Implies(rows[j][i] == 0,
                       curvature(effective, j) ==
                       2*z.If(root_parallel(j, neg), 1, 0)))
        for k in range(5):
            solver.add(midpoint_gradient(own, i, k) ==
                       z.RealVal(sum(k == v for v in pos)-sum(k == v for v in neg))/2)
            solver.add(ell[k]+midpoint_gradient(effective, i, k) ==
                       z.RealVal(sum(k == v for v in neg))/2)
        solver.add(value(own, i) == 0,
                   z.If(active[i], value(other, i) > 0, value(other, i) < 0))
    for i in (2, 3, 4):
        solver.add(value(cores[0], i) == 0, value(cores[1], i) == 0)

    if rigid:
        def comparator(coeff, i, pos, neg, scale=1):
            eqs = [z.Or(*[root_parallel(j, edge) for j in range(7)])
                   for edge in (pos, neg)]
            for j in range(7):
                eqs.append(z.Implies(rows[j][i] == 0,
                    curvature(coeff, j) == 2*scale*(z.If(root_parallel(j, pos), 1, 0)
                                                 -z.If(root_parallel(j, neg), 1, 0))))
            for k in range(5):
                eqs.append(midpoint_gradient(coeff, i, k) ==
                    scale*z.RealVal(sum(k == v for v in pos)-sum(k == v for v in neg))/2)
            return z.And(*eqs)

        def good(i):
            at_most_three = z.Sum(*[z.If(row[i] == 0, 1, 0) for row in rows]) <= 3
            all_root = z.And(*[z.Implies(row[i] == 0,
                z.Sum(*[z.If(t != 0, 1, 0) for t in row]) == 2) for row in rows])
            return z.Or(at_most_three, all_root)

        if kind != 'two_one_core':
            canonical = [[], []]
            for i in (2, 3, 4):
                for unique, owner, pos, neg in contacts:
                    if i in pos:
                        shared_pos = tuple(sorted((unique, next(v for v in pos if v != i))))
                        shared_neg = neg
                    else:
                        shared_pos = pos
                        shared_neg = tuple(sorted((unique, next(v for v in neg if v != i))))
                    canonical[owner].append(comparator(cores[owner], i, shared_pos, shared_neg))
                solver.add(z.Implies(good(i), z.Or(canonical[0][-1], canonical[1][-1])))
            # A core already canonical at its unique contact can be canonical
            # at at most one of the three shared contacts (eight-row bound).
            for conditions in canonical:
                for a, b in combinations(conditions, 2):
                    solver.add(z.Not(z.And(a, b)))
        else:
            conditions = []
            for i in (2, 3, 4):
                remaining = [k for k in range(5) if k != i]
                a = remaining[0]
                choices = []
                for b in remaining[1:]:
                    pos = (a, b)
                    neg = tuple(k for k in remaining if k not in pos)
                    choices += [comparator(cores[1], i, pos, neg, scale)
                                for scale in (-1, 1)]
                conditions.append(z.Or(*choices))
                # g already has two comparator germs and cannot supply a
                # third. Hence h is the sole effective fold, with unit scale.
                solver.add(z.Implies(good(i), conditions[-1]))
            solver.add(z.Not(z.And(*conditions)))

    # Established first-width support conditions, including arbitrary rows.
    for I in combinations(range(5), 4):
        for a in I:
            solver.add(z.Or(*[z.And(row[a] != 0,
                                      *[row[k] == 0 for k in range(5) if k not in I])
                              for row in rows]))
    for I in combinations(range(5), 3):
        solver.add(z.Or(*[z.And(*[row[k] == 0 for k in range(5) if k not in I])
                          for row in rows]))

    if wall:
        for j in range(m, 7):
            a = rows[j]
            both = z.And(curvature(cores[0], j) != 0,
                         curvature(cores[1], j) != 0)
            for pair in combinations(range(5), 2):
                triple = [k for k in range(5) if k not in pair]
                for sign in (-1, 1):
                    pattern = z.And(*[sign*a[k] > 0 for k in pair],
                                    *[sign*a[k] < 0 for k in triple])
                    allowed = z.Or(*[z.And(*[-sign*a[k] >= sign*a[i] for i in pair])
                                       for k in triple])
                    solver.add(z.Implies(z.And(both, pattern), allowed))

    booleans = [x for x in product((0, 1), repeat=5) if len(set(x)) > 1]
    if samples != 'none':
        points = booleans if samples == 'boolean' else [
            x for x in product((-1, 0, 1), repeat=5) if len(set(x)) > 1]
        for x in points:
            features = [relu(dot(row, x)) for row in rows]
            solver.add(dot(ell, x)+dot(remainder, features)
                       +relu(dot(cores[0], features))+relu(dot(cores[1], features)) == max(x))
    if shared_germs:
        # Directional derivatives at q_i, with gates of nonsingular first
        # rows frozen and singular first rows retaining their ReLU.
        for i in (2, 3, 4):
            for x in booleans:
                features = [z.If(row[i] < 0, dot(row, x),
                                  z.If(row[i] == 0, relu(dot(row, x)), 0))
                            for row in rows]
                solver.add(dot(ell, x)+dot(remainder, features)
                           +relu(dot(cores[0], features))+relu(dot(cores[1], features))
                           == max(x[k] for k in range(5) if k != i))
    variables = orient + [v for row in rows[m:] for v in row]
    variables += cores[0]+cores[1]+remainder+ell+active
    if supports is not None:
        # Known support zeroes remove most conditional curvature and gate
        # expressions before the nonlinear arithmetic solver sees them.
        simplified = z.SolverFor('QF_NRA')
        simplified.set(timeout=timeout)
        simplified.add(*[z.simplify(a) for a in solver.assertions()])
        solver = simplified
    return solver, variables, dict(kind=kind, mode=mode, samples=samples,
                                  shared_germs=shared_germs, wall=wall, rigid=rigid,
                                  mandatory_roots=edges, supports=supports,
                                  coefficient_gauge=coefficient_gauge)


def run(args):
    solver, variables, metadata = build(args.kind, args.mode, args.samples,
                                        args.shared_germs, not args.no_wall, args.timeout, args.rigid,
                                        coefficient_gauge=args.coefficient_gauge)
    name = 'max5_exact_three_shared_%s_%s_%s' % (args.kind, args.mode, args.samples)
    if args.shared_germs:
        name += '_germs'
    if not args.no_wall:
        name += '_wall'
    if args.rigid:
        name += '_rigid'
    if args.coefficient_gauge:
        name += '_cg'
    path = Path(__file__).with_name(name)
    path.with_suffix('.smt2').write_text(solver.to_smt2())
    if args.emit_only:
        print(json.dumps(dict(source=str(path.with_suffix('.smt2')), **metadata)), flush=True)
        return
    started = time.monotonic()
    result = solver.check()
    out = dict(status=str(result), elapsed=time.monotonic()-started, **metadata)
    if result == z.sat:
        model = solver.model()
        out['model'] = {str(v):str(model.eval(v, model_completion=True)) for v in variables}
    elif result == z.unknown:
        out['reason'] = solver.reason_unknown()
    path.with_suffix('.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--kind', choices=['one_each_same', 'one_each_path', 'two_one_core'], required=True)
    p.add_argument('--mode', choices=['general', 'distinct_nonroot'], default='general')
    p.add_argument('--samples', choices=['none', 'boolean', 'ternary'], default='boolean')
    p.add_argument('--shared-germs', action='store_true')
    p.add_argument('--no-wall', action='store_true')
    p.add_argument('--rigid', action='store_true')
    p.add_argument('--coefficient-gauge', action='store_true')
    p.add_argument('--timeout', type=int, default=60000)
    p.add_argument('--emit-only', action='store_true')
    run(p.parse_args())
