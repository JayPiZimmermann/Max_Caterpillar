#!/usr/bin/env python3
"""Exact orientation bookkeeping for reflected triangle-product orbits."""
from collections import defaultdict
from itertools import permutations
from pathlib import Path
import hashlib, json, random
import overnight_upper_triangle_attachments as attachment
import overnight_upper_triangle_fixed as fixed
import overnight_upper_product_family as base

HERE = Path(__file__).parent


def image_with_phase(descriptor, pi):
    images = []
    phase = 1
    for triangle, root, sign in descriptor:
        first, second = [i for i in triangle if i != root]
        if pi[first] > pi[second]:
            phase = -phase
        images.append((tuple(sorted(pi[v] for v in triangle)), pi[root], sign))
    phase *= (-1)**sum(images[i] > images[j]
                      for i in range(len(images)) for j in range(i+1, len(images)))
    return tuple(sorted(images)), phase


def canonical(n, descriptor):
    images = []
    for pi in fixed.group(n):
        target, phase = image_with_phase(descriptor, pi)
        images.append((target, phase*base.parity(pi)))
    target = min(d for d, _ in images)
    phases = {p for d, p in images if d == target}
    # Opposite phases at the same representative imply that its alternating
    # orbit sum is identically zero as a cubical chain.
    return target, (next(iter(phases)) if len(phases) == 1 else 0)


def transform(chain, pi):
    result = defaultdict(int)
    for (head, edges), coefficient in chain.items():
        def image(vector):
            answer = [0]*len(pi)
            for i, value in enumerate(vector):
                answer[pi[i]] = value
            return tuple(answer)
        item = base.normalize_cube(image(head), [image(e) for e in edges], coefficient)
        if item:
            result[item[0]] += item[1]
    return {k: v for k, v in result.items() if v}


def main():
    data = json.loads((HERE/'overnight_upper_two_page_witness_6.json').read_text())
    rng = random.Random(251041)
    permutations6 = list(permutations(range(6)))
    checks = 0
    for item in data['selected']:
        descriptor = item['descriptor']
        raw = attachment.raw_chain(6, descriptor)
        for pi in rng.sample(permutations6, 5):
            target, phase = image_with_phase(descriptor, pi)
            got = transform(raw, pi)
            expected = {k: phase*v for k, v in attachment.raw_chain(6, target).items()}
            assert got == expected
            checks += 1
        extended = tuple((tuple(t), r, s) for t, r, s in descriptor)+(((0, 5, 6), 0, 1),)
        target, phase = canonical(7, extended)
        base.raw_chain = attachment.raw_chain
        base.group = fixed.group
        original = base.sym_chain(7, extended)
        expected = {k: phase*v for k, v in base.sym_chain(7, target).items() if phase*v}
        assert original == expected
        checks += 1
    result = dict(status='EXACT_TRIANGLE_PRODUCT_ORIENTATION_CONTROLS_PASS', checks=checks,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (HERE/'overnight_upper_oriented_products.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result, flush=True)


if __name__ == '__main__':
    main()
