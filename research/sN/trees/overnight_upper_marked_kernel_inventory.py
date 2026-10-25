#!/usr/bin/env python3
"""Mark the future ear edge before projecting to its two-element stabilizer."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib, json, time
import overnight_upper_product_family as base
import overnight_upper_triangle_attachments as attachment
from overnight_upper_triangle_two_pages import two_pages

HERE = Path(__file__).parent
REFLECTION = tuple(5-i for i in range(6))


def projected_chain(descriptor, character):
    raw = attachment.raw_chain(6, descriptor)
    out = defaultdict(Q, raw)
    for (head, edges), coefficient in raw.items():
        def image(vector):
            result = [0]*6
            for i, value in enumerate(vector):
                result[REFLECTION[i]] = value
            return tuple(result)
        item = base.normalize_cube(image(head), [image(e) for e in edges],
                                   character*coefficient)
        if item:
            out[item[0]] += item[1]
    return {k: v for k, v in out.items() if v}


def main():
    start = time.monotonic()
    source = HERE/'overnight_upper_two_page_bundle.json'
    bundle = json.loads(source.read_text())
    templates = [r['descriptor'] for r in bundle['full_permutation_positive']]
    raw = set()
    for template in templates:
        for pi in permutations(range(6)):
            descriptor = attachment.image_descriptor(template, pi)
            if two_pages([t for t, _, _ in descriptor]):
                raw.add(descriptor)
    representatives = sorted({min(d, attachment.image_descriptor(d, REFLECTION)) for d in raw})
    sectors = []
    for character in (-1, 1):
        seen = set()
        descriptors = []
        zeros = 0
        for descriptor in representatives:
            chain = projected_chain(descriptor, character)
            if not chain:
                zeros += 1
                continue
            scale = next(iter(chain.values()))
            signature = tuple(sorted((key, value/scale) for key, value in chain.items()))
            if signature in seen:
                continue
            seen.add(signature)
            descriptors.append(descriptor)
        sectors.append(dict(character=character, descriptors=descriptors,
                            formally_zero_representatives=zeros,
                            role='particular lift and kernel' if character == -1 else 'kernel only'))
    result = dict(status='COMPLETE_MARKED_EDGE_TWO_CHARACTER_INVENTORY', n=6,
                  marked_attachment_edge=[0, 5], reflection=REFLECTION,
                  raw_descriptors=len(raw), reflection_orbit_representatives=len(representatives),
                  sectors=sectors,
                  source_bundle_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='The same six source types and exact fixed-order two-page filter as the positive N6 subfamily, with the future attachment edge marked. Both characters of its reflection stabilizer are retained. This is a complete inventory, not a sufficiency assertion.',
                  seconds=time.monotonic()-start)
    (HERE/'overnight_upper_marked_kernel_inventory_6.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('MARKED INVENTORY', len(raw), 'RAW', len(representatives), 'REFLECTION ORBITS',
          [(s['character'], len(s['descriptors'])) for s in sectors],
          'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
