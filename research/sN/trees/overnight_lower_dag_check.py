#!/usr/bin/env python3
"""Independently validate every state and summand of the N9 subset DAG.

No producer is imported. State identities are checked by exhaustive subset
partitions; root types are reconstructed directly from oriented tree edges.
The recurrence sums all bijections, counting equal children separately.
"""
import array
import collections
import gzip
import hashlib
import itertools
import json
from pathlib import Path
import struct
import time

HERE = Path(__file__).resolve().parent


def main():
    started = time.monotonic()
    manifest_path = HERE/'overnight_lower_dag_manifest_9.json.gz'
    with gzip.open(manifest_path, 'rt') as source:
        semantic = json.load(source)
    inventory_path = HERE/'overnight_lower_inventory_9.json'
    units = json.loads(inventory_path.read_text())['representatives']
    binary = HERE/'overnight_lower_dp_9.bin'
    with binary.open('rb') as source:
        magic, n, count, terms, columns, used_count = struct.unpack('<6Q', source.read(48))
        assert magic == 0x445053594D545245 and n == semantic['arity'] == 9
        arrays = []
        for size in (count+1, terms, terms, terms, columns, used_count):
            values = array.array('I')
            values.fromfile(source, size)
            assert values.itemsize == 4
            arrays.append(values)
        assert not source.read(1)
    offsets, left, right, bridge, roots, used = arrays
    labels = semantic['states']
    assert len(labels) == count+1 and labels[0] == ['one']
    types = semantic['types']
    canonical = []
    for i, (size, children) in enumerate(types):
        assert all(sign in (-1, 1) and 0 <= child < i for sign, child in children)
        assert size == 1+sum(types[child][0] for sign, child in children)
        canonical.append(tuple(sorted((sign, canonical[child]) for sign, child in children)))
    assert len(set(canonical)) == len(canonical)
    lookup = {}
    for state, label in enumerate(labels[1:], 1):
        kind, value, mask = label
        assert 0 < mask < (1 << (n-1))
        if kind == 'tree':
            assert types[value][0] == mask.bit_count() and types[value][0] > 1
            key = (kind, value, mask)
        else:
            assert kind == 'forest' and value
            assert all(sign in (-1, 1) and 0 <= child < len(types) for sign, child in value)
            assert sum(types[child][0] for sign, child in value) == mask.bit_count()
            key = (kind, tuple(map(tuple, value)), mask)
        assert key not in lookup
        lookup[key] = state

    def tree(typ, mask):
        assert types[typ][0] == mask.bit_count()
        return 0 if types[typ][0] == 1 else lookup['tree', typ, mask]

    def forest(children, mask):
        assert sum(types[child][0] for sign, child in children) == mask.bit_count()
        return lookup['forest', tuple(map(tuple, children)), mask] if children else 0

    for state, (kind, value, mask) in enumerate(labels[1:], 1):
        expected = []
        if kind == 'tree':
            for i in range(n-1):
                if mask & (1 << i):
                    expected.append((forest(types[value][1], mask ^ (1 << i)), 0, 0))
        else:
            sign, child = value[-1]
            bits = [1 << i for i in range(n-1) if mask & (1 << i)]
            for chosen in itertools.combinations(bits, types[child][0]):
                subset = sum(chosen)
                expected.append((tree(child, subset), forest(value[:-1], mask ^ subset),
                                 2*subset+int(sign == -1)))
        actual = [(left[j], right[j], bridge[j]) for j in range(offsets[state-1], offsets[state])]
        assert all(a < state and b < state for a, b, c in actual)
        assert collections.Counter(actual) == collections.Counter(expected), state
    assert sorted(set(bridge)-{0}) == list(used)
    assert len(units) == columns == len(roots) == 3822
    for unit, root_state in zip(units, roots):
        directed = set(map(tuple, unit['edges']))
        adjacency = {i: [] for i in range(1, n)}
        for a, b in directed:
            adjacency[a].append(b)
            adjacency[b].append(a)

        def rooted(v, parent):
            return tuple(sorted((1 if (w, v) in directed else -1, rooted(w, v))
                                for w in adjacency[v] if w != parent))

        expected = rooted(unit['root'], None)
        kind, typ, mask = labels[root_state]
        assert kind == 'tree' and mask == (1 << (n-1))-1 and canonical[typ] == expected
    result = dict(status='ALL_SUBSET_DAG_IDENTITIES_AND_ROOTS_PASS', arity=n,
                  states=count, summands=terms, roots=columns,
                  inventory_sha256=hashlib.sha256(inventory_path.read_bytes()).hexdigest(),
                  dag_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  semantics_sha256=hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  seconds=time.monotonic()-started,
                  scope='Recurrence and orbit sums only; no separation or rank claim')
    (HERE/'overnight_lower_dag_check_9.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
