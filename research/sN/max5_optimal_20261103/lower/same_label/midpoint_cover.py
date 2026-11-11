"""Exact support count for the q3+q4 midpoint obstruction.

Checks a finite support predicate only. The analytical implication is a
separate proof; this script does not prove any network theorem.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SOURCE = ROOT/'research/sN/frontier5/max5_three_shared_one_each_cover.json'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    cover = json.loads(SOURCE.read_text())['kinds']['three_roots']['records']
    rows = []
    residual = []
    for index, row in enumerate(cover):
        if row['status'] != 'REMAINS':
            continue
        supports = row['supports']
        missing_crossing = all(len(s) == 2 or not {3, 4} <= set(s) for s in supports)
        # Independent bitmask spelling includes all physical rows and permits
        # repeated copies of the root34, with either physical orientation.
        mask_test = all((sum(1 << i for i in s) & 24) != 24 or set(s) == {3, 4}
                        for s in supports)
        assert missing_crossing == mask_test
        if missing_crossing:
            rows.append(dict(index=index, supports=supports,
                             physical_roots=sum(len(s) == 2 for s in supports)))
        else:
            residual.append(index)
    counts = Counter(row['physical_roots'] for row in rows)
    assert len(rows) == 225 and len(residual) == 162
    assert counts == {3: 4, 4: 47, 5: 107, 6: 67}
    minimum = [row['index'] for row in rows if row['physical_roots'] == 3]
    assert minimum == [275, 307, 353, 355]
    out = dict(status='EXACT_MIDPOINT_SUPPORT_PREDICATE_COUNT_PASS',
               scope='Finite support count; analytical obstruction is a separate dependency.',
               source=str(SOURCE.relative_to(ROOT)), source_sha256=sha(SOURCE),
               checker_sha256=sha(__file__), total=387, covered=225,
               remaining=162, root_histogram=dict(counts),
               minimal_root_indices=minimum, records=rows,
               residual_indices=residual)
    (HERE/'midpoint_cover_receipt.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({k: v for k, v in out.items() if k not in ('records', 'residual_indices')}))

if __name__ == '__main__':
    main()
