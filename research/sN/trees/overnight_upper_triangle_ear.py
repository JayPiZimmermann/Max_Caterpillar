#!/usr/bin/env python3
"""One exterior-ear step from the eight exact two-page N6 product types."""
from itertools import product
from pathlib import Path
import hashlib, json, tempfile
import overnight_upper_triangle_fixed as probe
import overnight_upper_triangle_attachments as attachment

HERE = Path(__file__).parent


def main():
    witness_path = HERE/'overnight_upper_two_page_witness_6.json'
    witness = json.loads(witness_path.read_text())
    representatives = set()
    for item in witness['selected']:
        for pi in probe.group(6):
            old = attachment.image_descriptor(item['descriptor'], pi)
            for root, sign in product((0, 5, 6), (-1, 1)):
                descriptor = tuple(sorted(old + (((0, 5, 6), root, sign),)))
                representatives.add(min(attachment.image_descriptor(descriptor, g)
                                        for g in probe.group(7)))
    representatives = sorted(representatives)
    shapes = sorted({tuple(t for t, _, _ in d) for d in representatives})
    print('EAR INVENTORY', len(representatives), 'D7 PRODUCT ORBITS',
          len(shapes), 'SHAPES', flush=True)
    probe.inventory = lambda n: (shapes, representatives)
    with tempfile.TemporaryDirectory(prefix='max-caterpillar-ear-') as temp:
        probe.HERE = Path(temp)
        probe.main(7)
        record = json.loads((Path(temp)/'overnight_upper_triangle_fixed_7.json').read_text())
    record['shared_probe_sha256'] = record.pop('producer_sha256')
    record['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    record['source_witness_sha256'] = hashlib.sha256(witness_path.read_bytes()).hexdigest()
    record['scope'] = 'N7 exterior-ear products from all D6 images of the eight exact N6 two-page product types, all three new-triangle attachment vertices and both reflections, then D7 averaging. Every graph retains two noncrossing pages. This is a restricted recurrence test, not the full two-page family.'
    record['status'] = record['status'].replace('FIXED_ORDER', 'EXTERIOR_EAR')
    (HERE/'overnight_upper_triangle_ear_7.json').write_text(json.dumps(record, separators=(',', ':'))+'\n')
    print('EAR RESULT', record['status'], record['ranks'], flush=True)


if __name__ == '__main__':
    main()
