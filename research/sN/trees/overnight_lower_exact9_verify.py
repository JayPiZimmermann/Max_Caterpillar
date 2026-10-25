#!/usr/bin/env python3
"""Stream the complete saved N9 exact rows and independently check the rank proof.

The two exact evaluation engines and separate DAG/domain checkers establish
entry semantics. This checker independently replays every rational kernel
relation and modular reduction, checks complete row coverage and binds all
those stages. It does not infer a rational rank from modular rank alone.
Run only after all83 campaign chunks exist. Large rows remain local caches.
"""
from pathlib import Path
from fractions import Fraction
import gzip
import hashlib
import json
import math
import struct
import time

HERE = Path(__file__).resolve().parent
CHUNKS = HERE / 'overnight_lower_exact9_chunks'
PRIME = 1000003


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as handle:
        for block in iter(lambda: handle.read(1 << 20), b''):
            result.update(block)
    return result.hexdigest()


def read(name):
    return json.loads((HERE / name).read_text())


def main():
    start = time.monotonic()
    proposal = read('overnight_lower_matching_rank_9.json')
    indices = proposal['selected_row_indices']
    points = proposal['selected_points']
    pivot_columns = proposal['column_pivots']
    assert len(indices) == len(set(indices)) == len(points) == 1971
    assert len(pivot_columns) == len(set(pivot_columns)) == 1971
    assert pivot_columns[-1] == 3822
    pivots = set(pivot_columns[:-1])
    assert all(0 <= j < 3822 for j in pivots)

    config_path = CHUNKS / 'config.json'
    config = json.loads(config_path.read_text())
    bound_sources = {
        'rank_proposal_sha256': 'overnight_lower_matching_rank_9.json',
        'relation_sha256': 'overnight_lower_kernel9_crt.jsonl.gz',
        'dag_sha256': 'overnight_lower_dp_9.bin',
        'semantic_check_sha256': 'overnight_lower_dag_check_9.json',
        'rational_source_sha256': 'overnight_lower_rational_dp.cpp',
        'integer_source_sha256': 'overnight_lower_integer_dp.cpp',
        'runner_sha256': 'overnight_lower_exact9_run.py',
    }
    for field, name in bound_sources.items():
        assert config[field] == digest(HERE / name), name
    config_hash = digest(config_path)

    relations = []
    free = set()
    with gzip.open(HERE / 'overnight_lower_kernel9_crt.jsonl.gz', 'rt') as handle:
        for line in handle:
            record = json.loads(line)
            j = record['free_column']
            entries = record['coefficients']
            assert j not in free and j not in pivots and 0 <= j < 3822
            assert entries[0] == [j, 1, 1]
            assert len({i for i, _, _ in entries}) == len(entries)
            assert all(i in pivots and den > 0 for i, _, den in entries[1:])
            fractions = [(i, Fraction(num, den)) for i, num, den in entries]
            common = math.lcm(*(c.denominator for _, c in fractions))
            relations.append(tuple((i, c.numerator * (common // c.denominator))
                                   for i, c in fractions))
            free.add(j)
    assert len(relations) == len(free) == 1852
    assert free | pivots == set(range(3822))

    inventory = read('overnight_lower_inventory_check_9.json')
    semantic = read('overnight_lower_dag_check_9.json')
    minor = read('overnight_lower_minor_check_9.json')
    assert inventory['status'] == 'INDEPENDENT_COMPLETE_INVENTORY_CHECK_PASS'
    assert inventory['function_orbits'] == 3822
    assert semantic['status'] == 'ALL_SUBSET_DAG_IDENTITIES_AND_ROOTS_PASS'
    assert semantic['roots'] == 3822
    assert inventory['checker_sha256'] == digest(HERE / 'overnight_lower_inventory_check.py')
    assert semantic['checker_sha256'] == digest(HERE / 'overnight_lower_dag_check.py')
    assert semantic['semantics_sha256'] == digest(HERE / 'overnight_lower_dag_manifest_9.json.gz')
    assert semantic['inventory_sha256'] == inventory['inventory_sha256']
    assert inventory['inventory_sha256'] == digest(HERE / 'overnight_lower_inventory_9.json')
    assert semantic['dag_sha256'] == config['dag_sha256']
    assert minor['status'] == 'NONZERO_AUGMENTED_MINOR_MOD_PRIME'
    assert minor['prime'] == PRIME and minor['dimension'] == 1971
    assert 0 < minor['determinant'] < PRIME
    assert minor['rank_proposal_sha256'] == config['rank_proposal_sha256']
    assert minor['minor_sha256'] == digest(HERE / 'overnight_lower_augmented_minor_9.bin')
    matrix = HERE / 'overnight_lower_matching_matrix_9.u32'
    assert digest(matrix) == minor['matrix_sha256'] == proposal['matrix_sha256']
    assert minor['checker_cpp_sha256'] == digest(HERE / 'overnight_lower_minor_check.cpp')
    assert minor['checker_python_sha256'] == digest(HERE / 'overnight_lower_minor_check.py')

    chunk_records = []
    total = 0
    with matrix.open('rb') as modular:
        for chunk_index, first in enumerate(range(0, 1971, 24)):
            end = min(first + 24, 1971)
            stem = CHUNKS / ('chunk_%03d' % chunk_index)
            receipt_path = stem.with_suffix('.check.json')
            receipt = json.loads(receipt_path.read_text())
            assert receipt['status'] == 'DOUBLE_EXACT_ARITHMETIC_AND_KERNELS_PASS'
            assert (receipt['first_row'], receipt['end_row'], receipt['rows']) == (first, end, end-first)
            assert receipt['relations_per_row'] == 1852
            assert receipt['config_sha256'] == config_hash
            assert [p['algorithm'] for p in receipt['processes']] == ['rational', 'integer']
            for process in receipt['processes']:
                assert process['exit_code'] == 0
                log = stem.with_suffix('.' + process['algorithm'] + '.log')
                assert digest(log) == process['log_sha256']
            compressed = stem.with_suffix('.jsonl.gz')
            assert digest(compressed) == receipt['compressed_sha256']
            raw_hash = hashlib.sha256()
            count = 0
            with gzip.open(compressed, 'rb') as handle:
                for raw in handle:
                    raw_hash.update(raw)
                    record = json.loads(raw)
                    assert first + count == total < end
                    assert record['index'] == count and record['point'] == points[total]
                    scale = int(record['scale'])
                    values = tuple(map(int, record['values']))
                    assert len(values) == 3823 and scale > 0 and scale % PRIME
                    assert math.gcd(scale, *values) == 1
                    modular.seek(indices[total] * 3823 * 4)
                    residues = struct.unpack('<3823I', modular.read(3823 * 4))
                    factor = scale % PRIME
                    assert all(v % PRIME == w * factor % PRIME for v, w in zip(values, residues))
                    for relation in relations:
                        assert sum(values[i] * coefficient for i, coefficient in relation) == 0
                    total += 1
                    count += 1
            assert count == end - first
            assert raw_hash.hexdigest() == receipt['rational_integer_output_sha256']
            chunk_records.append({'first_row': first, 'end_row': end,
                                  'receipt_sha256': digest(receipt_path),
                                  'data_sha256': receipt['compressed_sha256']})
            print('INDEPENDENT_ROW_CHECK', total, '/1971', round(time.monotonic()-start, 2), flush=True)
    assert total == 1971 and len(chunk_records) == 83
    result = {
        'status': 'INDEPENDENT_COMPLETE_N9_EXACT_RANK_CERTIFICATE_PASS',
        'arity': 9, 'rows': 1971, 'ordinary_columns': 3822,
        'independent_rational_relations': 1852,
        'ordinary_rank': 1970, 'augmented_rank': 1971,
        'modular_augmented_determinant': minor['determinant'], 'prime': PRIME,
        'config_sha256': config_hash, 'checker_sha256': digest(Path(__file__)),
        'inventory_check_sha256': digest(HERE/'overnight_lower_inventory_check_9.json'),
        'dag_check_sha256': digest(HERE/'overnight_lower_dag_check_9.json'),
        'minor_check_sha256': digest(HERE/'overnight_lower_minor_check_9.json'),
        'chunks': chunk_records, 'seconds': time.monotonic()-start,
        'scope': 'Exact finite separation of max9 from all canonical eight-vertex trees without a perfect matching, with all roots/orientations/apex labels. Saved evaluations have two exact arithmetic implementations and an independently checked recurrence/domain. This checker replays all exact kernel relations, all modular reductions and all row coverage. The uniform counting bridge yields a polynomial, not exponential, all-tree bound. Not Lean.',
    }
    (HERE/'overnight_lower_exact9_verify.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(result['status'], flush=True)


if __name__ == '__main__':
    main()
