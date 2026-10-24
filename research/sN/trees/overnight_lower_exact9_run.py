#!/usr/bin/env python3
"""Bounded, resumable N9 exact finite-evaluation certificate campaign.

Three workers; each chunk has at most 24 rows. Each arithmetic invocation
has a 1000-second timeout and a 3-GiB address-space cap. A six-hour campaign
deadline stops new chunks. Completed chunks are independently checked by
GMP rational and common-denominator integer arithmetic, then compressed.
The retained proof uses 1852 independent column relations, not a giant
rational annihilator. Nothing here asserts a uniform odd-arity theorem.
"""
import concurrent.futures
import gzip
import hashlib
import json
import math
from pathlib import Path
import shutil
import subprocess
import threading
import time

import numpy as np

HERE = Path(__file__).resolve().parent
OUT = HERE/'overnight_lower_exact9_chunks'
PRIME = 1000003
CHUNK = 24
WORKERS = 3
CAP_SECONDS = 21600


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as source:
        while data := source.read(1 << 20):
            h.update(data)
    return h.hexdigest()


def main():
    started = time.monotonic()
    OUT.mkdir(exist_ok=True)
    rank_path = HERE/'overnight_lower_matching_rank_9.json'
    rank = json.loads(rank_path.read_text())
    assert rank['modular_ranks'] == [1970, 1971]
    selected = rank['selected_row_indices']
    points = rank['selected_points']
    assert len(selected) == len(points) == 1971 and len(set(selected)) == 1971
    pivots = set(rank['column_pivots'][:-1])
    assert len(pivots) == 1970 and rank['column_pivots'][-1] == 3822
    relation_path = HERE/'overnight_lower_kernel9_crt.jsonl.gz'
    relations = []
    free = set()
    with gzip.open(relation_path, 'rt') as source:
        for line in source:
            relation = json.loads(line)
            j = relation['free_column']
            coefficients = relation['coefficients']
            assert j not in free and j not in pivots and 0 <= j < 3822
            assert coefficients[0] == [j, 1, 1]
            assert len({i for i, n, d in coefficients}) == len(coefficients)
            assert all(i in pivots and d > 0 for i, n, d in coefficients[1:])
            denominator = math.lcm(*(d for i, n, d in coefficients))
            relations.append(tuple((i, n*(denominator//d)) for i, n, d in coefficients))
            free.add(j)
    assert len(relations) == 1852 and free | pivots == set(range(3822))
    semantics = json.loads((HERE/'overnight_lower_dag_check_9.json').read_text())
    assert semantics['status'] == 'ALL_SUBSET_DAG_IDENTITIES_AND_ROOTS_PASS'
    dag = HERE/'overnight_lower_dp_9.bin'
    assert digest(dag) == semantics['dag_sha256']
    baseline = np.memmap(HERE/'overnight_lower_matching_matrix_9.u32', mode='r', dtype='<u4', shape=(3854, 3823))
    config = dict(status='CONFIGURED_EXACT_FINITE_CERTIFICATE_NOT_YET_PROVED', arity=9,
                  rows=1971, columns=3822, independent_kernel_relations=1852,
                  workers=WORKERS, chunk_rows=CHUNK, per_process_seconds=1000,
                  per_process_memory_bytes=3*1024**3, campaign_seconds=CAP_SECONDS,
                  rank_proposal_sha256=digest(rank_path), relation_sha256=digest(relation_path),
                  dag_sha256=digest(dag), semantic_check_sha256=digest(HERE/'overnight_lower_dag_check_9.json'),
                  rational_source_sha256=digest(HERE/'overnight_lower_rational_dp.cpp'),
                  integer_source_sha256=digest(HERE/'overnight_lower_integer_dp.cpp'),
                  runner_sha256=digest(Path(__file__)))
    config_path = OUT/'config.json'
    if config_path.exists():
        assert json.loads(config_path.read_text()) == config, 'sources changed; preserve old campaign before restarting'
    else:
        config_path.write_text(json.dumps(config, indent=2)+'\n')
    stop = threading.Event()

    def chunk(start):
        index = start//CHUNK
        end = min(start+CHUNK, len(points))
        stem = OUT/f'chunk_{index:03}'
        receipt_path = stem.with_suffix('.check.json')
        compressed = stem.with_suffix('.jsonl.gz')
        if receipt_path.exists():
            receipt = json.loads(receipt_path.read_text())
            assert receipt['status'] == 'DOUBLE_EXACT_ARITHMETIC_AND_KERNELS_PASS'
            assert receipt['first_row'] == start and receipt['end_row'] == end
            assert digest(compressed) == receipt['compressed_sha256']
            return receipt
        if stop.is_set() or time.monotonic()-started > CAP_SECONDS-2100:
            return dict(status='NOT_STARTED', first_row=start, end_row=end)
        begin = time.monotonic()
        point_file = stem.with_suffix('.points.txt')
        point_file.write_text(f'{end-start} 9\n'+'\n'.join(' '.join(map(str, x)) for x in points[start:end])+'\n')
        rational = stem.with_suffix('.rational.jsonl')
        integer = stem.with_suffix('.integer.jsonl')
        results = []
        try:
            for name, output in [('rational', rational), ('integer', integer)]:
                command = ['prlimit', '--as='+str(3*1024**3), '--',
                           '/tmp/overnight_lower_'+name+'_dp', str(dag), str(point_file), str(output)]
                log_path = stem.with_suffix('.'+name+'.log')
                with log_path.open('w') as log:
                    result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=1000)
                results.append(dict(algorithm=name, exit_code=result.returncode, log_sha256=digest(log_path)))
                assert result.returncode == 0, (index, name, result.returncode)
                if name == 'rational':
                    seen = 0
                    with rational.open() as source:
                        for local, line in enumerate(source):
                            row = json.loads(line)
                            absolute = start+local
                            assert absolute < end and row['index'] == local and row['point'] == points[absolute]
                            scale = int(row['scale'])
                            values = list(map(int, row['values']))
                            assert len(values) == 3823 and scale > 0 and scale % PRIME
                            assert math.gcd(scale, *values) == 1
                            expected = baseline[selected[absolute]]
                            assert all(v % PRIME == int(b)*(scale % PRIME) % PRIME for v, b in zip(values, expected))
                            for number, relation in enumerate(relations):
                                assert sum(values[j]*coefficient for j, coefficient in relation) == 0, (absolute, number)
                            seen += 1
                    assert seen == end-start
            assert digest(rational) == digest(integer), 'different exact arithmetic outputs'
            raw_hash = digest(rational)
            with rational.open('rb') as source, gzip.open(compressed, 'wb', compresslevel=6) as dest:
                shutil.copyfileobj(source, dest)
            receipt = dict(status='DOUBLE_EXACT_ARITHMETIC_AND_KERNELS_PASS', first_row=start,
                           end_row=end, rows=end-start, relations_per_row=len(relations),
                           rational_integer_output_sha256=raw_hash,
                           compressed_sha256=digest(compressed), processes=results,
                           config_sha256=digest(config_path), seconds=time.monotonic()-begin)
            receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
            rational.unlink()
            integer.unlink()
            print('CHUNK_PASS', index, 'ROWS', start, end, 'SECONDS', round(time.monotonic()-begin, 2), flush=True)
            return receipt
        except Exception as error:
            stop.set()
            result = dict(status='FAILED_NO_PROOF', first_row=start, end_row=end,
                          error=repr(error), seconds=time.monotonic()-begin, processes=results)
            stem.with_suffix('.failure.json').write_text(json.dumps(result, indent=2)+'\n')
            print('CHUNK_FAILED', index, repr(error), flush=True)
            return result

    with concurrent.futures.ThreadPoolExecutor(max_workers=WORKERS) as pool:
        results = list(pool.map(chunk, range(0, len(points), CHUNK)))
    passed = [r for r in results if r['status'] == 'DOUBLE_EXACT_ARITHMETIC_AND_KERNELS_PASS']
    complete = len(passed) == len(results)
    receipt = dict(status='EXACT_ROWS_AND_INDEPENDENT_KERNELS_PASS' if complete else 'INCOMPLETE_NO_N9_PROOF',
                   completed_rows=sum(r['rows'] for r in passed), expected_rows=len(points),
                   completed_chunks=len(passed), expected_chunks=len(results),
                   exact_column_rank_upper_bound=1970 if complete else None,
                   next_gate='Independent modular augmented-minor rank check and reviewed counting bridge',
                   config_sha256=digest(config_path), seconds=time.monotonic()-started,
                   chunk_receipts=[dict(first_row=r['first_row'], status=r['status']) for r in results])
    (HERE/'overnight_lower_exact9_run.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == '__main__':
    main()
