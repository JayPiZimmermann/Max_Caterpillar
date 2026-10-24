#!/usr/bin/env python3
"""Independent arithmetic/normalization controls and C++ DP timing receipt."""
import hashlib
import itertools
import json
import math
from pathlib import Path
import resource
import subprocess
import time

import numpy as np

HERE = Path(__file__).parent
P = 1000003
ENGINE = Path('/tmp/overnight_lower_dp_engine')


def main():
    started = time.monotonic()
    compile_data = json.loads((HERE / 'overnight_lower_dp_9_compile.json').read_text())
    inventory_path = HERE / 'overnight_lower_inventory_9.json'
    inventory = json.loads(inventory_path.read_text())
    assert compile_data['source_sha256'] == hashlib.sha256(inventory_path.read_bytes()).hexdigest()
    point = compile_data['benchmark_point']
    points_path = HERE / 'overnight_lower_dp_9_timing_points.txt'
    points_path.write_text('16 9\n' + (' '.join(map(str, point)) + '\n') * 16)
    output = HERE / 'overnight_lower_dp_9_timing.u32'
    subprocess.run(['g++', '-O3', '-std=c++17', str(HERE / 'overnight_lower_dp_engine.cpp'), '-o', str(ENGINE)], check=True)
    before = time.monotonic()
    result = subprocess.run([str(ENGINE), str(HERE / 'overnight_lower_dp_9.bin'), str(points_path), str(output)],
                            text=True, capture_output=True, check=True)
    elapsed = time.monotonic() - before
    (HERE / 'overnight_lower_dp_9_timing.log').write_text(result.stdout)
    matrix = np.fromfile(output, dtype=np.uint32).reshape(16, len(compile_data['benchmark_row']) + 1)
    assert all(row[:-1].tolist() == compile_data['benchmark_row'] for row in matrix)
    expected_target = pow(math.prod(point) % P, -1, P)
    assert np.all(matrix[:, -1] == expected_target)
    # Independent complete-S9 controls via normalized heads and positive-endpoint cuts.
    permutations = np.array(list(itertools.permutations(range(9))), dtype=np.int64)
    assigned = np.array(point, dtype=np.int64)[permutations]
    apex = assigned[:, 0]
    inverse = np.zeros(P, dtype=np.int64)
    inverse[1] = 1
    for j in range(2, P):
        inverse[j] = P - (P // j) * inverse[P % j] % P
    numerator = np.ones(len(permutations), dtype=np.int64)
    for _ in range(5):
        numerator = numerator * (-apex % P) % P
    checked = []
    for index in (0, len(inventory['representatives']) // 2, len(inventory['representatives']) - 1):
        unit = inventory['representatives'][index]
        h = [0] * 9
        h[0], h[unit['root']] = -1, 1
        edges = []
        for u, v in unit['edges']:
            if u > v:
                h[u] += 1
                h[v] -= 1
                u, v = v, u
            edges.append((u, v))
        denominator = np.ones(len(permutations), dtype=np.int64)
        for u, v in edges:
            component, pending = {u}, [u]
            while pending:
                w = pending.pop()
                for i, j in edges:
                    if (i, j) == (u, v):
                        continue
                    z = j if i == w else i if j == w else None
                    if z is not None and z not in component:
                        component.add(z)
                        pending.append(z)
            assert v not in component
            q = assigned[:, sorted(component)].sum(axis=1)
            H = sum(h[j] for j in component)
            denominator = denominator * ((q + H * apex) % P) % P
            denominator = denominator * ((q + (H + 1) * apex) % P) % P
        assert np.all(denominator)
        value = int((numerator * inverse[denominator] % P).sum() % P)
        assert value == int(matrix[0, index])
        checked.append(index)
    d7 = json.loads((HERE / 'overnight_lower_matching_rows_7.json').read_text())
    p7 = HERE / 'overnight_lower_dp_7_control_points.txt'
    o7 = HERE / 'overnight_lower_dp_7_controls.u32'
    subprocess.run([str(ENGINE), str(HERE / 'overnight_lower_dp_7.bin'), str(p7), str(o7)], check=True, capture_output=True)
    rows7 = np.fromfile(o7, dtype=np.uint32).reshape(5, 259)
    for row, index in zip(rows7, (0, 1, 10, 50, 112)):
        assert row.tolist() == d7['modular_rows'][index]
    receipt = dict(status='COMPILED_DP_INDEPENDENT_CONTROLS_PASS', prime=P,
                   n9_columns=3822, n9_states=compile_data['states'], n9_terms=compile_data['terms'],
                   n9_complete_permutation_controls=checked, permutations_per_control=math.factorial(9),
                   n9_python_cpp_complete_row_matches=16,
                   n7_complete_stored_rows_checked=5, n7_entries_per_row=259,
                   n9_cpp_16_rows_seconds=elapsed, n9_cpp_seconds_per_row=elapsed / 16,
                   estimated_3854_row_seconds=elapsed / 16 * 3854,
                   child_peak_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                   cpp_source_sha256=hashlib.sha256((HERE / 'overnight_lower_dp_engine.cpp').read_bytes()).hexdigest(),
                   dag_source_sha256=hashlib.sha256((HERE / 'overnight_lower_dp.py').read_bytes()).hexdigest(),
                   benchmark_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   inventory_sha256=hashlib.sha256(inventory_path.read_bytes()).hexdigest(),
                   elapsed_seconds=time.monotonic() - started)
    (HERE / 'overnight_lower_dp_benchmark.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == '__main__':
    main()
