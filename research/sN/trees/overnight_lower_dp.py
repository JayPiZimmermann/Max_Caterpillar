#!/usr/bin/env python3
"""Shared signed-subtree/forest subset DP for full symmetric tree Fourier sums.

The DAG contains sums of products and edge factors. It is independent of
frequency values, so all unit representatives and all apex assignments share
the same compiled states. No permutation enumeration is used in evaluation.
"""
from fractions import Fraction as Q
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import struct
import sys
import time

import numpy as np

HERE = Path(__file__).parent
PRIME = 1000003


class Compiler:
    def __init__(self, arity):
        self.arity = arity
        self.m = arity - 1
        self.types = [(1, ())]
        self.type_lookup = {(): 0}
        self.function_states = {}
        self.forest_states = {}
        self.starts = [0]
        self.left, self.right, self.bridge = [], [], []
        self.subsets = {}

    def unit_type(self, unit):
        edges = set(map(tuple, unit['edges']))
        vertices = set(v for edge in edges for v in edge)
        adjacency = {v: [] for v in vertices}
        for u, v in edges:
            adjacency[u].append(v)
            adjacency[v].append(u)

        def visit(v, parent):
            children = []
            for w in adjacency[v]:
                if w != parent:
                    child = visit(w, v)
                    children.append((1 if (w, v) in edges else -1, child))
            # Small subtree prefixes are shared by many full tree types.
            key = tuple(sorted(children, key=lambda item: (self.types[item[1]][0], item[0], item[1])))
            if key not in self.type_lookup:
                self.type_lookup[key] = len(self.types)
                self.types.append((1 + sum(self.types[t][0] for sign, t in key), key))
            return self.type_lookup[key]

        root = visit(unit['root'], None)
        assert self.types[root][0] == self.m
        return root

    def append(self, terms):
        for left, right, bridge in terms:
            self.left.append(left)
            self.right.append(right)
            self.bridge.append(bridge)
        self.starts.append(len(self.left))
        return len(self.starts) - 1

    def choices(self, mask, size):
        key = (mask, size)
        if key not in self.subsets:
            bits = [1 << i for i in range(self.m) if mask >> i & 1]
            self.subsets[key] = [sum(t) for t in itertools.combinations(bits, size)]
        return self.subsets[key]

    def function(self, typ, mask):
        size, children = self.types[typ]
        assert mask.bit_count() == size
        if size == 1:
            return 0  # Constant one: one bijection of a singleton.
        key = (typ, mask)
        if key not in self.function_states:
            terms = [(self.forest(children, mask ^ (1 << i)), 0, 0)
                     for i in range(self.m) if mask >> i & 1]
            self.function_states[key] = self.append(terms)
        return self.function_states[key]

    def forest(self, children, mask):
        if not children:
            assert not mask
            return 0
        key = (children, mask)
        if key not in self.forest_states:
            sign, typ = children[-1]
            rest = children[:-1]
            terms = []
            for subset in self.choices(mask, self.types[typ][0]):
                terms.append((self.function(typ, subset), self.forest(rest, mask ^ subset),
                              2 * subset + int(sign == -1)))
            self.forest_states[key] = self.append(terms)
        return self.forest_states[key]

    def compile(self, units):
        types = [self.unit_type(unit) for unit in units]
        roots = [self.function(typ, (1 << self.m) - 1) for typ in types]
        used = sorted(set(self.bridge) - {0})
        return DAG(self.arity, self.starts, self.left, self.right, self.bridge, roots, used,
                   dict(signed_subtree_types=len(self.types), function_states=len(self.function_states),
                        forest_states=len(self.forest_states)))


class DAG:
    def __init__(self, arity, starts, left, right, bridge, roots, used, diagnostics=None):
        self.arity, self.m = arity, arity - 1
        self.starts, self.left, self.right, self.bridge = starts, left, right, bridge
        self.roots, self.used = roots, used
        self.diagnostics = diagnostics or {}

    def save(self, path):
        arrays = [self.starts, self.left, self.right, self.bridge, self.roots, self.used]
        with path.open('wb') as output:
            output.write(struct.pack('<6Q', 0x445053594D545245, self.arity, len(self.starts) - 1,
                                     len(self.left), len(self.roots), len(self.used)))
            for values in arrays:
                output.write(np.asarray(values, dtype='<u4').tobytes())

    def evaluate(self, point, prime=PRIME):
        assert len(point) == self.arity and sum(point) == 0
        total = [0] * len(self.roots)
        for apex in range(self.arity):
            a = point[apex]
            frequencies = [point[i] for i in range(self.arity) if i != apex]
            sums = [0] * (1 << self.m)
            for mask in range(1, len(sums)):
                bit = mask & -mask
                sums[mask] = sums[mask ^ bit] + frequencies[bit.bit_length() - 1]
            factors = [0] * (2 << self.m)
            factors[0] = 1
            for index in self.used:
                q = sums[index // 2]
                sign = -1 if index & 1 else 1
                den = q * (q + sign * a)
                factors[index] = pow(den % prime, -1, prime) if prime else Q(1, den)
            values = [1] + [0] * (len(self.starts) - 1)
            for state in range(1, len(values)):
                value = 0
                for term in range(self.starts[state - 1], self.starts[state]):
                    value += values[self.left[term]] * values[self.right[term]] * factors[self.bridge[term]]
                    if prime:
                        value %= prime
                values[state] = value
            prefactor = (-a) ** (self.arity - 4)
            for j, root in enumerate(self.roots):
                total[j] += prefactor * values[root]
                if prime:
                    total[j] %= prime
        return total


def controls():
    from gluing_review import kernel, pruefer_tree
    started = time.monotonic()
    rng = random.Random(24102579)
    units = []
    for _ in range(24):
        tree = [(u + 1, v + 1) for u, v in pruefer_tree(4, [rng.randrange(4), rng.randrange(4)])]
        edges = [e[::-1] if rng.randrange(2) else e for e in tree]
        units.append(dict(root=rng.randrange(1, 5), edges=edges))
    compiler = Compiler(5)
    dag = compiler.compile(units)
    point = [-40, 1, 3, 9, 27]
    exact = dag.evaluate(point, prime=None)
    for unit, value in zip(units, exact):
        brute = Q(0)
        for pi in itertools.permutations(range(5)):
            frequencies = {j: point[pi[j]] for j in range(5)}
            a = frequencies[0]
            brute += -a * kernel(range(1, 5), unit['edges'], frequencies, a, unit['root'])
        assert value == brute
    mod = dag.evaluate(point)
    assert mod == [q.numerator * pow(q.denominator, -1, PRIME) % PRIME for q in exact]
    source = HERE / 'overnight_lower_matching_rows_7.json'
    data = json.loads(source.read_text())
    compiler = Compiler(7)
    dag7 = compiler.compile(data['representatives'])
    timings = []
    for index in (0, 1, 10, 50, len(data['points']) - 1):
        before = time.monotonic()
        values = dag7.evaluate(data['points'][index])
        timings.append(time.monotonic() - before)
        assert values == data['modular_rows'][index][:-1]
        scale = int(data['scales'][index])
        assert [v * scale % PRIME for v in values] == [int(v) % PRIME for v in data['integer_rows'][index][:-1]]
    dag7.save(HERE / 'overnight_lower_dp_7.bin')
    result = dict(status='EXACT_N5_AND_COMPLETE_N7_ROW_CONTROLS_PASS',
                  n5_fraction_permutation_controls=len(units), n7_complete_rows=5, n7_columns=len(dag7.roots),
                  n7_states=len(dag7.starts) - 1, n7_terms=len(dag7.left),
                  n7_python_row_seconds=timings, n7_diagnostics=dag7.diagnostics,
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  elapsed_seconds=time.monotonic() - started)
    (HERE / 'overnight_lower_dp_controls.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


def compile_nine():
    started = time.monotonic()
    source = HERE / 'overnight_lower_inventory_9.json'
    inventory = json.loads(source.read_text())
    compiler = Compiler(9)
    dag = compiler.compile(inventory['representatives'])
    binary = HERE / 'overnight_lower_dp_9.bin'
    dag.save(binary)
    result = dict(status='COMPILED_DAG_NO_SPAN_CLAIM', arity=9, columns=len(dag.roots),
                  states=len(dag.starts) - 1, terms=len(dag.left), used_edge_factors=len(dag.used),
                  diagnostics=dag.diagnostics, compile_seconds=time.monotonic() - started,
                  binary_bytes=binary.stat().st_size,
                  binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    point = [-sum(range(10, 18))] + list(range(10, 18))
    before = time.monotonic()
    values = dag.evaluate(point)
    result.update(python_row_seconds=time.monotonic() - before, benchmark_point=point,
                  benchmark_row=values)
    (HERE / 'overnight_lower_dp_9_compile.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'benchmark_row'}, indent=2), flush=True)


if __name__ == '__main__':
    {'controls': controls, 'compile9': compile_nine}[sys.argv[1]]()
