"""Exact all-input equality checker for rational piecewise-affine circuits.

The JSON format supports affine nodes, ReLU, and selectors with a specified
>= 0 or > 0 tie convention.  Ordinary activation patches are compiled by
reusing source-run nodes in a base run.  Explicit piecewise-affine distributed
translations can be compiled into the same language.  All arithmetic and all
feasibility decisions use Fraction and Fourier--Motzkin elimination.

Usage:
  python research/sN/frontierN/causal_intervention_certifier.py specification.json --output receipt.json

A PASS quantifies over every input satisfying the listed weak/strict affine
domain constraints, including lower-dimensional boundary cells.  A FAIL has
an exact rational witness, independently reevaluated through the original DAG.
This is executable mathematical certification, not a Lean-verified checker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path


def dot(a, x):
    return sum((c * y for c, y in zip(a[:-1], x)), a[-1])


def negate(a):
    return tuple(-c for c in a)


@dataclass(frozen=True)
class Constraint:
    form: tuple[Q, ...]  # coefficients followed by the affine constant
    strict: bool = False

    def satisfied(self, x):
        v = dot(self.form, x)
        return v > 0 if self.strict else v >= 0


def canonical(rows):
    """Normalize only by positive factors; a strict duplicate dominates."""
    merged = {}
    for row in rows:
        a = tuple(Q(c) for c in row.form)
        if not any(a[:-1]):
            good = a[-1] > 0 if row.strict else a[-1] >= 0
            if not good:
                return None
            continue
        scale = next(abs(c) for c in a if c)
        a = tuple(c / scale for c in a)
        merged[a] = merged.get(a, False) or row.strict
    return tuple(Constraint(a, strict) for a, strict in sorted(merged.items()))


class ExactFeasibility:
    def __init__(self):
        self.cache = {}
        self.calls = 0
        self.eliminations = 0

    def solve(self, rows, dimension):
        """Return a rational witness, or None for exact infeasibility."""
        self.calls += 1
        clean = canonical(rows)
        if clean is None:
            return None
        key = (dimension, clean)
        if key in self.cache:
            return self.cache[key]
        if dimension == 0:
            result = ()
        elif not clean:
            result = (Q(0),) * dimension
        else:
            self.eliminations += 1
            index = dimension - 1
            pos = [r for r in clean if r.form[index] > 0]
            neg = [r for r in clean if r.form[index] < 0]
            projected = [Constraint(r.form[:index] + (r.form[-1],), r.strict)
                         for r in clean if r.form[index] == 0]
            for p in pos:
                for n in neg:
                    ap, an = p.form[index], n.form[index]
                    combined = tuple((-an) * p.form[j] + ap * n.form[j]
                                     for j in range(dimension + 1) if j != index)
                    projected.append(Constraint(combined, p.strict or n.strict))
            prefix = self.solve(projected, dimension - 1)
            if prefix is None:
                result = None
            else:
                lowers, uppers = [], []
                for row in clean:
                    coefficient = row.form[index]
                    remainder = dot(row.form[:index] + (row.form[-1],), prefix)
                    if coefficient > 0:
                        lowers.append((-remainder / coefficient, row.strict))
                    elif coefficient < 0:
                        uppers.append((-remainder / coefficient, row.strict))
                lo = max((v for v, _ in lowers), default=None)
                hi = min((v for v, _ in uppers), default=None)
                if lo is not None and hi is not None:
                    if lo == hi:
                        assert not any(s for v, s in lowers + uppers if v == lo)
                        last = lo
                    else:
                        assert lo < hi
                        last = (lo + hi) / 2
                elif lo is not None:
                    last = lo + 1
                elif hi is not None:
                    last = hi - 1
                else:
                    last = Q(0)
                result = prefix + (last,)
                assert all(r.satisfied(result) for r in clean)
        self.cache[key] = result
        return result


def evaluate(spec, point):
    values = {name: Q(value) for name, value in zip(spec["inputs"], point)}
    for node in spec["nodes"]:
        op = node["op"]
        if op == "linear":
            value = sum((Q(c) * values[name] for c, name in node.get("terms", [])),
                        Q(node.get("const", 0)))
        elif op == "relu":
            value = max(Q(0), values[node["arg"]])
        elif op in ("select_ge", "select_gt"):
            v = values[node["guard"]]
            active = v >= 0 if op == "select_ge" else v > 0
            value = values[node["then"] if active else node["else"]]
        else:
            raise ValueError(f"unsupported operation {op!r}")
        values[node["id"]] = value
    return values


def certify(spec):
    def reject_float(value):
        if isinstance(value, float):
            raise ValueError("use integers or rational strings, not floating-point coefficients")
        if isinstance(value, dict):
            for item in value.values():
                reject_float(item)
        elif isinstance(value, list):
            for item in value:
                reject_float(item)

    reject_float(spec)
    names = spec["inputs"]
    n = len(names)
    if len(set(names)) != n:
        raise ValueError("input names must be distinct")
    zero = (Q(0),) * (n + 1)
    initial = {name: tuple(Q(int(i == j)) for j in range(n)) + (Q(0),)
               for i, name in enumerate(names)}
    by_id = {}
    known = set(names)
    for node in spec["nodes"]:
        key = node["id"]
        if key in known:
            raise ValueError(f"duplicate node {key}")
        op = node["op"]
        if op == "linear":
            dependencies = [name for _, name in node.get("terms", [])]
        elif op == "relu":
            dependencies = [node["arg"]]
        elif op in ("select_ge", "select_gt"):
            dependencies = [node["guard"], node["then"], node["else"]]
        else:
            raise ValueError(f"unsupported operation {op!r}")
        if not set(dependencies) <= known:
            raise ValueError(f"forward or unknown dependency at {key}")
        known.add(key)
        by_id[key] = (node, dependencies)
    needed = set()

    def require(key):
        if key in needed:
            return
        if key not in known:
            raise ValueError(f"unknown output {key}")
        needed.add(key)
        if key in by_id:
            for dependency in by_id[key][1]:
                require(dependency)

    for pair in spec["equal"]:
        if len(pair) != 2:
            raise ValueError("each equality must have two node names")
        for key in pair:
            require(key)
    nodes = [node for node in spec["nodes"] if node["id"] in needed]
    domain = []
    for row in spec.get("domain", []):
        a = [Q(0)] * n + [Q(row.get("const", 0))]
        for c, key in row.get("terms", []):
            if key not in names:
                raise ValueError("domain constraints may use only input variables")
            a[names.index(key)] += Q(c)
        domain.append(Constraint(tuple(a), bool(row.get("strict", False))))
    feasibility = ExactFeasibility()
    stats = {"nodes": len(nodes), "branches": 0, "feasible_cells": 0,
             "infeasible_branches": 0, "identity_checks": 0}
    witness = None
    feasible_domain = feasibility.solve(domain, n)

    def visit(index, values, rows):
        nonlocal witness
        if index == len(nodes):
            stats["feasible_cells"] += 1
            for left, right in spec["equal"]:
                difference = tuple(a - b for a, b in zip(values[left], values[right]))
                if not any(difference):
                    continue
                # Even a nonzero affine expression can vanish on a boundary cell.
                for sign in (1, -1):
                    stats["identity_checks"] += 1
                    point = feasibility.solve(rows + [Constraint(tuple(sign*c for c in difference), True)], n)
                    if point is not None:
                        actual = evaluate(spec, point)
                        assert all(r.satisfied(point) for r in domain)
                        assert actual[left] != actual[right]
                        witness = {"inputs": {name: str(x) for name, x in zip(names, point)},
                                   "left": left, "right": right,
                                   "left_value": str(actual[left]),
                                   "right_value": str(actual[right]),
                                   "difference": str(actual[left] - actual[right])}
                        return False
            return True
        node = nodes[index]
        op, key = node["op"], node["id"]
        if op == "linear":
            form = [Q(0)] * n + [Q(node.get("const", 0))]
            for c, arg in node.get("terms", []):
                form = [a + Q(c) * b for a, b in zip(form, values[arg])]
            return visit(index + 1, values | {key: tuple(form)}, rows)
        guard = values[node["arg"] if op == "relu" else node["guard"]]
        if not any(guard):
            if op == "relu":
                value = zero
            else:
                value = values[node["then"] if op == "select_ge" else node["else"]]
            return visit(index + 1, values | {key: value}, rows)
        positive_strict = op == "select_gt"
        for active in (True, False):
            stats["branches"] += 1
            constraint = Constraint(guard if active else negate(guard),
                                    positive_strict if active else not positive_strict)
            extended = rows + [constraint]
            if feasibility.solve(extended, n) is None:
                stats["infeasible_branches"] += 1
                continue
            value = (guard if active else zero) if op == "relu" else values[node["then"] if active else node["else"]]
            if not visit(index + 1, values | {key: value}, extended):
                return False
        return True

    passed = feasible_domain is None or visit(0, initial, domain)
    stats.update(feasibility_calls=feasibility.calls, fm_eliminations=feasibility.eliminations)
    digest = hashlib.sha256(json.dumps(spec, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"name": spec.get("name", "unnamed"), "status": "PASS" if passed else "FAIL",
            "domain_empty": feasible_domain is None, "spec_sha256": digest,
            "stats": stats, "counterexample": witness}


class Builder:
    """Convenience compiler; the checker itself consumes the plain JSON DAG."""
    def __init__(self, inputs):
        self.inputs = list(inputs)
        self.nodes = []
        self.memo = {}

    def node(self, op, **fields):
        key = json.dumps([op, fields], sort_keys=True)
        if key not in self.memo:
            name = f"n{len(self.nodes)}"
            self.nodes.append({"id": name, "op": op, **fields})
            self.memo[key] = name
        return self.memo[key]

    def linear(self, terms=(), const=0):
        combined = {}
        for coefficient, name in terms:
            combined[name] = combined.get(name, Q(0)) + Q(coefficient)
        terms = [[str(c), name] for name, c in sorted(combined.items()) if c]
        if len(terms) == 1 and terms[0][0] == "1" and not Q(const):
            return terms[0][1]
        return self.node("linear", terms=terms, const=str(Q(const)))

    def relu(self, node):
        return self.node("relu", arg=node)

    def selector(self, guard, positive, negative, strict=False):
        return self.node("select_gt" if strict else "select_ge", guard=guard,
                         then=positive, **{"else": negative})

    def network(self, net, inputs, patches=None):
        patches = patches or {}
        if len(inputs) != net["N"]:
            raise ValueError("network input count disagrees with N")
        h1, h2 = len(net["first_layer"]), len(net["second_layer"])
        if (any(len(row) != len(inputs) for row in net["first_layer"])
                or any(len(row) != h1 for row in net["second_layer"])
                or len(net["output"]) != h2):
            raise ValueError("inconsistent network matrix dimensions")
        if any(layer not in (0, 1) or not 0 <= index < (h1 if layer == 0 else h2)
               for layer, index in patches):
            raise ValueError("patch target is outside the two hidden layers")
        first = []
        for i, row in enumerate(net["first_layer"]):
            first.append(patches.get((0, i)) or self.relu(self.linear(zip(row, inputs))))
        second = []
        for i, row in enumerate(net["second_layer"]):
            second.append(patches.get((1, i)) or self.relu(self.linear(zip(row, first))))
        out = self.linear(zip(net["output"], second))
        return first, second, out

    def specification(self, name, equal, domain=()):
        return {"name": name, "inputs": self.inputs, "nodes": self.nodes,
                "domain": list(domain), "equal": list(equal)}



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("specification", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = certify(json.loads(args.specification.read_text()))
    result["checker_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(result, indent=2))
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    raise SystemExit(int(result["status"] != "PASS"))


if __name__ == "__main__":
    main()
