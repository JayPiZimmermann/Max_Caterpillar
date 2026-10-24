#!/usr/bin/env python3
"""Emit semantic state labels for independent checking of the subset DAG."""
import gzip
import json
from pathlib import Path
from overnight_lower_dp import Compiler

HERE = Path(__file__).resolve().parent
inventory = json.loads((HERE/'overnight_lower_inventory_9.json').read_text())
compiler = Compiler(9)
dag = compiler.compile(inventory['representatives'])
labels = [None]*len(dag.starts)
labels[0] = ['one']
for (typ, mask), state in compiler.function_states.items():
    assert labels[state] is None
    labels[state] = ['tree', typ, mask]
for (children, mask), state in compiler.forest_states.items():
    assert labels[state] is None
    labels[state] = ['forest', children, mask]
assert all(x is not None for x in labels)
with gzip.open(HERE/'overnight_lower_dag_manifest_9.json.gz', 'wt') as output:
    json.dump(dict(arity=9, types=compiler.types, states=labels), output)
print('semantic labels', len(labels), 'types', len(compiler.types), flush=True)
