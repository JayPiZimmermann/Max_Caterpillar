"""Exact all-input Max_N verification without second-layer cell enumeration.

Input is a bias-free two-hidden-layer network with rational coefficients:
N, first_layer, second_layer, output. Arbitrary first directions are allowed.
This checker partitions only by the winning input and first hyperplanes.
On each open cell it groups crossing second-layer ridges, checks signed
curvature cancellation, then checks the remaining linear gradient. Full
Euclidean input domain and continuity extend the result to every boundary.

No floating point is used. FAIL includes a rational input reevaluated in
the original network. INCOMPLETE (an optional budget) is never exclusion.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

CORE = Path(__file__).resolve().parents[1] / "frontierN" / "causal_intervention_certifier.py"
_spec = importlib.util.spec_from_file_location("_max5_exact_feasibility", CORE)
_core = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _core
_spec.loader.exec_module(_core)
Constraint, ExactFeasibility = _core.Constraint, _core.ExactFeasibility


def dot(a, x):
    return sum((c * v for c, v in zip(a, x)), Q(0))


def negative(a):
    return tuple(-c for c in a)


def split_normal(a):
    """a=scale*normal, with the first nonzero normal entry equal to +1."""
    scale = next((c for c in a if c), None)
    return None if scale is None else (tuple(c / scale for c in a), scale)


def reject_floats(value):
    if isinstance(value, float):
        raise ValueError("use exact integers or rational strings, not floats")
    if isinstance(value, dict):
        for item in value.values():
            reject_floats(item)
    elif isinstance(value, list):
        for item in value:
            reject_floats(item)


def read_network(data):
    reject_floats(data)
    n = data["N"]
    if not isinstance(n, int) or n < 1:
        raise ValueError("N must be a positive integer")
    for key in ("bias", "biases", "first_bias", "first_biases", "second_bias", "second_biases", "output_bias"):
        if key in data:
            raise ValueError("this checker accepts the bias-free schema only")
    a = [tuple(Q(c) for c in row) for row in data["first_layer"]]
    w = [tuple(Q(c) for c in row) for row in data["second_layer"]]
    d = tuple(Q(c) for c in data["output"])
    if any(len(row) != n for row in a) or any(len(row) != len(a) for row in w) or len(d) != len(w):
        raise ValueError("inconsistent network dimensions")
    return n, a, w, d


def evaluate(network, x):
    n, a, w, d = network
    x = tuple(Q(c) for c in x)
    assert len(x) == n
    first = [max(Q(0), dot(row, x)) for row in a]
    pre = [dot(row, first) for row in w]
    value = sum((c * max(Q(0), v) for c, v in zip(d, pre)), Q(0))
    return value, first, pre


def safe_step(point, direction, forms):
    """Preserve every currently nonzero form's sign under both perturbations."""
    bounds = [Q(1)]
    for row in forms:
        old, change = dot(row, point), dot(row, direction)
        if old and change:
            bounds.append(abs(old) / (2 * abs(change)))
    return min(bounds)


class BudgetExpired(Exception):
    pass


def certify(data, seconds=None, max_cells=None):
    started = time.monotonic()
    network = read_network(data)
    n, a, w, d = network
    solver = ExactFeasibility()
    stats = {"first_cells": 0, "first_hyperplanes": 0, "crossing_groups": 0,
             "feasibility_requests": 0, "reused_interior_witnesses": 0}
    normals, normal_indices, row_codes = [], {}, []
    for row in a:
        split = split_normal(row)
        if split is None:
            row_codes.append(None)
            continue
        normal, coefficient = split
        if normal not in normal_indices:
            normal_indices[normal] = len(normals)
            normals.append(normal)
        row_codes.append((normal_indices[normal], coefficient))
    stats["first_hyperplanes"] = len(normals)
    failure = None

    def check_budget():
        if seconds is not None and time.monotonic() - started > seconds:
            raise BudgetExpired

    def feasible(rows, hint=None):
        check_budget()
        stats["feasibility_requests"] += 1
        if hint is not None and all(dot(row, hint) > 0 for row in rows):
            stats["reused_interior_witnesses"] += 1
            return hint
        return solver.solve([Constraint(tuple(row) + (Q(0),), True) for row in rows], n)

    def witness_record(point, reason, winner, extra=None):
        value, first, pre = evaluate(network, point)
        target = max(point)
        assert value != target, "a failure certificate must fail direct exact evaluation"
        assert point[winner] == target
        result = {"reason": reason, "winner": winner,
                  "input": [str(v) for v in point], "network_value": str(value),
                  "target_value": str(target), "error": str(value - target),
                  "first_activations": [str(v) for v in first],
                  "second_preactivations": [str(v) for v in pre]}
        if extra:
            result.update(extra)
        return result

    def gradient_witness(point, constraints, difference, winner):
        if dot(difference, point):
            return witness_record(point, "wrong remaining linear gradient", winner)
        i = next(i for i, c in enumerate(difference) if c)
        direction = tuple(Q(j == i) for j in range(n))
        step = safe_step(point, direction, constraints)
        moved = tuple(x + step * v for x, v in zip(point, direction))
        assert all(dot(row, moved) > 0 for row in constraints)
        return witness_record(moved, "wrong remaining linear gradient", winner)

    def ridge_witness(normal, group, constraints, pre, winner):
        # Opposite witnesses form a rational strict-cell point on this wall.
        positive, neg = group["positive"], group["negative"]
        p, q = dot(normal, positive), dot(normal, neg)
        assert p > 0 > q
        point = tuple((p * y - q * x) / (p - q) for x, y in zip(positive, neg))
        assert not dot(normal, point) and all(dot(row, point) > 0 for row in constraints)

        # Move within the wall off every other distinct second-layer wall.
        others = [row for row in pre if any(row) and split_normal(row)[0] != normal]
        vanishing = [row for row in others if not dot(row, point)]
        pivot = next(i for i, c in enumerate(normal) if c)
        if vanishing:
            basis = []
            for j in range(n):
                if j == pivot:
                    continue
                v = [Q(0)] * n
                v[j], v[pivot] = Q(1), -normal[j] / normal[pivot]
                basis.append(tuple(v))
            assert basis
            for t in range(1, len(vanishing) * max(1, len(basis) - 1) + 2):
                direction = tuple(sum((Q(t)**k * row[i] for k, row in enumerate(basis)), Q(0))
                                  for i in range(n))
                if all(dot(row, direction) for row in vanishing):
                    break
            else:
                raise AssertionError("nonzero wall polynomials cannot vanish at every selected t")
            step = safe_step(point, direction, constraints + others)
            point = tuple(x + step * v for x, v in zip(point, direction))
        assert not dot(normal, point)
        assert all(dot(row, point) > 0 for row in constraints)
        assert all(dot(row, point) for row in others)

        direction = tuple(Q(i == pivot) for i in range(n))
        step = safe_step(point, direction, constraints + others)
        points = [point] + [tuple(x + sign * step * v for x, v in zip(point, direction))
                            for sign in (1, -1)]
        for candidate in points:
            assert all(dot(row, candidate) > 0 for row in constraints)
            if evaluate(network, candidate)[0] != max(candidate):
                return witness_record(candidate, "uncancelled crossing ridge", winner,
                                      {"ridge_normal": [str(c) for c in normal],
                                       "ridge_curvature": str(group["curvature"])})
        raise AssertionError("nonzero centered second difference must yield a counterexample")

    def cell(winner, constraints, signs, point):
        nonlocal failure
        if max_cells is not None and stats["first_cells"] >= max_cells:
            raise BudgetExpired
        stats["first_cells"] += 1
        active = [code is not None and code[1] * signs[code[0]] > 0 for code in row_codes]
        pre = [tuple(sum((weights[j] * a[j][i] for j in range(len(a)) if active[j]), Q(0))
                     for i in range(n)) for weights in w]
        linear = [Q(0)] * n
        groups = {}
        for row, output in zip(pre, d):
            if not output or not any(row):
                continue
            value = dot(row, point)
            positive = point if value > 0 else feasible(constraints + [row], point)
            neg = point if value < 0 else feasible(constraints + [negative(row)], point)
            if neg is None:
                assert positive is not None
                linear = [x + output * c for x, c in zip(linear, row)]
                continue
            if positive is None:
                continue
            normal, coefficient = split_normal(row)
            group = groups.setdefault(normal, {"curvature": Q(0), "positive": None, "negative": None})
            group["curvature"] += output * abs(coefficient)
            if coefficient > 0:
                group["positive"], group["negative"] = positive, neg
            else:
                group["positive"], group["negative"] = neg, positive
                linear = [x + output * c for x, c in zip(linear, row)]
        stats["crossing_groups"] += len(groups)
        for normal, group in groups.items():
            if group["curvature"]:
                failure = ridge_witness(normal, group, constraints, pre, winner)
                return False
        difference = [c - Q(i == winner) for i, c in enumerate(linear)]
        if any(difference):
            failure = gradient_witness(point, constraints, difference, winner)
            return False
        return True

    def refine(winner, index, constraints, signs, point):
        check_budget()
        if index == len(normals):
            return cell(winner, constraints, signs, point)
        for sign in (1, -1):
            row = tuple(sign * c for c in normals[index])
            extended = constraints + [row]
            witness = feasible(extended, point)
            if witness is not None and not refine(winner, index + 1, extended, signs + [sign], witness):
                return False
        return True

    status = "PASS"
    try:
        for winner in range(n):
            constraints = [tuple(Q(i == winner) - Q(i == loser) for i in range(n))
                           for loser in range(n) if loser != winner]
            point = tuple(Q(i == winner) for i in range(n))
            if not refine(winner, 0, constraints, [], point):
                status = "FAIL"
                break
    except BudgetExpired:
        status = "INCOMPLETE"
    stats.update(exact_feasibility_calls=solver.calls, fm_eliminations=solver.eliminations,
                 seconds=time.monotonic() - started)
    return {"status": status, "N": n, "h1": len(a), "h2": len(w),
            "scope": "all real inputs; bias-free two-hidden-layer rational network",
            "method": "winner/first-layer open cells, exact grouped crossing-ridge cancellation, continuity",
            "stats": stats, "counterexample": failure,
            "network_sha256": hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
            "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "feasibility_core_sha256": hashlib.sha256(CORE.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("network", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--seconds", type=float)
    parser.add_argument("--max-cells", type=int)
    args = parser.parse_args()
    result = certify(json.loads(args.network.read_text()), args.seconds, args.max_cells)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["status"] == "PASS" else (1 if result["status"] == "FAIL" else 2))


if __name__ == "__main__":
    main()
