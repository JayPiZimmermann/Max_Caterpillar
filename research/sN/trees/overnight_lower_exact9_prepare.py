#!/usr/bin/env python3
"""Rebuild local binaries and modular caches for the recorded N9 proposal.

Run with the existing h5-growth Python environment after compiling the DAG
with overnight_lower_dp.py compile9. Recorded proposals are preserved if
present. Each subprocess has its own declared timeout; no network is used.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def run(command, seconds):
    print('RUN', command, 'BUDGET', seconds, flush=True)
    subprocess.run(command, check=True, timeout=seconds)


def main():
    rank = json.loads((HERE/'overnight_lower_matching_rank_9.json').read_text())
    points = rank['selected_points']
    selected = HERE/'overnight_lower_integer_selected_points_9.txt'
    selected.write_text(f'{len(points)} 9\n'+'\n'.join(' '.join(map(str, x)) for x in points)+'\n')
    for name in ('dp_engine', 'rational_dp', 'integer_dp', 'minor_check'):
        source = HERE/f'overnight_lower_{name}.cpp'
        target = '/tmp/overnight_lower_'+name
        libraries = ['-lgmpxx', '-lgmp'] if name in ('rational_dp', 'integer_dp') else []
        run(['g++', '-O3', '-std=c++17', str(source), *libraries, '-o', target], 60)
    matrix = HERE/'overnight_lower_matching_matrix_9.u32'
    if not matrix.exists():
        run(['/tmp/overnight_lower_dp_engine', str(HERE/'overnight_lower_dp_9.bin'),
             str(HERE/'overnight_lower_matching_points_9.txt'), str(matrix)], 600)
    assert hashlib.sha256(matrix.read_bytes()).hexdigest() == rank['matrix_sha256']
    proposal = HERE/'overnight_lower_kernel9_crt.jsonl.gz'
    if not proposal.exists():
        prime2 = 1000033
        assert all(prime2 % i for i in range(2, 1001))
        source = (HERE/'overnight_lower_dp_engine.cpp').read_text()
        assert source.count('P = 1000003;') == 1
        temporary = Path('/tmp/overnight_lower_dp_prime2.cpp')
        temporary.write_text(source.replace('P = 1000003;', 'P = 1000033;'))
        run(['g++', '-O3', '-std=c++17', str(temporary), '-o', '/tmp/overnight_lower_dp_prime2'], 60)
        run(['/tmp/overnight_lower_dp_prime2', str(HERE/'overnight_lower_dp_9.bin'), str(selected),
             str(HERE/'overnight_lower_matching_prime2_9.u32')], 600)
        run([sys.executable, str(HERE/'overnight_lower_kernel9.py'), 'crt'], 180)
    print('LOCAL_CACHES_READY; exact campaign and independent minor checks remain separate', flush=True)


if __name__ == '__main__':
    main()
