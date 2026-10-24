#!/usr/bin/env python3
"""Exact finite-field rank diagnostic for the complete nine-label inventory.

Prime 1000003, 3854 declared rows, 3822 full-symmetry columns. A rank gap
is only a proposal for a rational separator. No rational rank upper bound
or all-arity theorem is inferred. Budget 1200 seconds, one FLINT thread.
"""
import hashlib
import json
from pathlib import Path
import time

import numpy as np
from flint import ctx, nmod_mat

HERE = Path(__file__).resolve().parent
PRIME = 1000003


def pivot_columns(matrix, rank):
    out = []
    cursor = 0
    for i in range(rank):
        while cursor < matrix.ncols() and matrix[i, cursor] == 0:
            cursor += 1
        assert cursor < matrix.ncols()
        out.append(cursor)
        cursor += 1
    return out


def main():
    started = time.monotonic()
    ctx.threads = 1
    config = json.loads((HERE/'overnight_lower_matching_run_9.json').read_text())
    rows, columns = config['rows'], config['columns']
    path = HERE/'overnight_lower_matching_matrix_9.u32'
    assert path.stat().st_size == rows*(columns+1)*4
    data = np.fromfile(path, dtype='<u4').reshape(rows, columns+1)
    assert int(data.max()) < PRIME
    matrix = nmod_mat(data.tolist(), PRIME)
    del data
    reduced, rank_augmented = matrix.rref()
    pivots = pivot_columns(reduced, rank_augmented)
    rank_ordinary = rank_augmented-int(columns in pivots)
    print('MODULAR RANKS', rank_ordinary, rank_augmented,
          'seconds', round(time.monotonic()-started, 3), flush=True)
    result = dict(arity=9, max_matching=3, prime=PRIME, rows=rows,
                  function_orbits=columns, modular_ranks=[rank_ordinary, rank_augmented],
                  status='MODULAR_DIAGNOSTIC_ONLY',
                  column_pivots=pivots, budget_seconds=1200,
                  matrix_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  config_sha256=hashlib.sha256((HERE/'overnight_lower_matching_run_9.json').read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    del reduced
    if rank_augmented > rank_ordinary:
        transposed, rank_transposed = matrix.transpose().rref()
        assert rank_transposed == rank_augmented
        selected = pivot_columns(transposed, rank_transposed)
        source = (HERE/'overnight_lower_matching_points_9.txt').read_text().splitlines()
        assert source[0] == f'{rows} 9'
        result['selected_row_indices'] = selected
        result['selected_points'] = [list(map(int, source[i+1].split())) for i in selected]
        result['next_gate'] = 'Exact rational evaluation and independently checked annihilator required'
    result['seconds'] = time.monotonic()-started
    assert result['seconds'] < 1200
    out = HERE/'overnight_lower_matching_rank_9.json'
    out.write_text(json.dumps(result, indent=2)+'\n')
    print('DONE', {k:v for k,v in result.items() if k not in
                   ('column_pivots','selected_row_indices','selected_points')}, flush=True)


if __name__ == '__main__':
    main()
