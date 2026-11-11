"""Independent enumeration of the support predicate in the midpoint proof.

This checks the frozen cover's records, not the geometric exhaustiveness of
that earlier cover and not the mathematical network implication.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SOURCE = ROOT / 'research/sN/frontier5/max5_three_shared_one_each_cover.json'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

data = json.loads(SOURCE.read_text())['kinds']['three_roots']['records']
indices = []
histogram = Counter()
total = 0
for i, record in enumerate(data):
    if record['status'] != 'REMAINS':
        continue
    total += 1
    supports = [frozenset(row) for row in record['supports']]
    # List the actual nonlinear obstructions: a row spanning both lower
    # labels, with at least one other label. All root34 copies are permitted.
    problematic = [s for s in supports if 3 in s and 4 in s and len(s) > 2]
    if not problematic:
        indices.append(i)
        histogram[sum(len(s) == 2 for s in supports)] += 1

assert total == 387
assert len(indices) == 225
assert dict(histogram) == {3: 4, 4: 47, 5: 107, 6: 67}
old = json.loads((HERE.parent / 'same_label/midpoint_cover_receipt.json').read_text())
assert indices == [row['index'] for row in old['records']]
receipt = dict(
    status='INDEPENDENT_MIDPOINT_SUPPORT_COUNT_PASS',
    scope='Support predicate only; cover exhaustiveness and geometric implication are separate.',
    source=str(SOURCE.relative_to(ROOT)), source_sha256=sha(SOURCE),
    checker_sha256=sha(Path(__file__)),
    total=total, covered=len(indices), remaining=total-len(indices),
    physical_root_histogram=dict(histogram), covered_indices=indices,
    primary_count_sha256=sha(HERE.parent / 'same_label/midpoint_cover_receipt.json'),
)
(HERE / 'midpoint_support_secondary_receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k != 'covered_indices'}))
