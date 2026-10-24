#!/usr/bin/env python3
"""Extract the proposed augmented minor and run the independent scalar gate."""
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import numpy as np

HERE = Path(__file__).resolve().parent
rank_path = HERE/'overnight_lower_matching_rank_9.json'
proposal = json.loads(rank_path.read_text())
rows = proposal['selected_row_indices']
columns = proposal['column_pivots']
assert len(rows) == len(columns) == len(set(rows)) == len(set(columns)) == 1971
assert columns[-1] == 3822 and all(0 <= j < 3822 for j in columns[:-1])
source = HERE/'overnight_lower_matching_matrix_9.u32'
assert hashlib.sha256(source.read_bytes()).hexdigest() == proposal['matrix_sha256']
data = np.memmap(source, dtype='<u4', mode='r', shape=(3854, 3823))
minor = HERE/'overnight_lower_augmented_minor_9.bin'
with minor.open('wb') as output:
    output.write(struct.pack('<Q', 1971))
    for i in rows:
        output.write(np.asarray(data[i, columns], dtype='<u4').tobytes())
receipt_path = HERE/'overnight_lower_minor_check_9.json'
result = subprocess.run(['/tmp/overnight_lower_minor_check', str(minor), str(receipt_path)], timeout=300)
assert result.returncode == 0
receipt = json.loads(receipt_path.read_text())
assert receipt['status'] == 'NONZERO_AUGMENTED_MINOR_MOD_PRIME'
assert receipt['dimension'] == 1971 and 0 < receipt['determinant'] < receipt['prime'] == 1000003
receipt.update(minor_sha256=hashlib.sha256(minor.read_bytes()).hexdigest(),
               matrix_sha256=proposal['matrix_sha256'],
               rank_proposal_sha256=hashlib.sha256(rank_path.read_bytes()).hexdigest(),
               checker_cpp_sha256=hashlib.sha256((HERE/'overnight_lower_minor_check.cpp').read_bytes()).hexdigest(),
               checker_python_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               scope='Rational augmented rank lower bound after exact row/reduction checks; no ordinary rank upper bound here')
receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2), flush=True)
