#!/usr/bin/env python3
"""Inventory non-ear two-page triangle grafts on the eight exact N6 types."""
from itertools import combinations, product
from pathlib import Path
import hashlib, json, time
import overnight_upper_triangle_fixed as fixed
import overnight_upper_triangle_attachments as attachment
from overnight_upper_triangle_two_pages import two_pages

HERE = Path(__file__).parent


def main():
    start = time.monotonic()
    source = HERE/'overnight_upper_two_page_witness_6.json'
    witness = json.loads(source.read_text())
    representatives = set()
    raw = allowed = 0
    for item in witness['selected']:
        for pi in fixed.group(6):
            old = attachment.image_descriptor(item['descriptor'], pi)
            for u, v in combinations(range(6), 2):
                triangle = (u, v, 6)
                if not two_pages([t for t, _, _ in old]+[triangle]):
                    raw += 6
                    continue
                for root, sign in product(triangle, (-1, 1)):
                    raw += 1
                    allowed += 1
                    descriptor = tuple(sorted(old+((triangle, root, sign),)))
                    representatives.add(min(attachment.image_descriptor(descriptor, g)
                                            for g in fixed.group(7)))
    representatives = sorted(representatives)
    shapes = sorted({tuple(t for t, _, _ in d) for d in representatives})
    result = dict(status='COMPLETE_TWO_PAGE_TRIANGLE_GRAFT_SUBFAMILY_INVENTORY', n=7,
                  raw_choices=raw, two_page_choices=allowed, descriptors=representatives,
                  triangle_shapes=shapes,
                  source_witness_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='All D6 images of the eight exact N6 types, one new triangle containing label 6 and any two old labels, all roots/reflections, retain exactly the two-page compatible choices, then quotient by D7.',
                  seconds=time.monotonic()-start)
    (HERE/'overnight_upper_triangle_grafts_7_inventory.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('GRAFT INVENTORY', raw, 'RAW', allowed, 'TWO PAGE', len(representatives),
          'D7 ORBITS', len(shapes), 'SHAPES', 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
