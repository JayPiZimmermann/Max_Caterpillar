#!/usr/bin/env python3
"""Two-page fixed-order subfamily from the six exact S6 positive types.

No full permutation averaging is used in a column. Permutations enumerate
which labelings of the six source types fit two pages in the one fixed
cyclic order; only D6 sums then enter the probe.
"""
from itertools import combinations, permutations
from pathlib import Path
import hashlib, json, tempfile
import overnight_upper_triangle_fixed as probe
import overnight_upper_triangle_attachments as attachment

HERE = Path(__file__).parent


def incompatible(a, b):
    return any(probe.base.crosses(e, f)
               for e in combinations(a, 2) for f in combinations(b, 2))


def two_pages(triangles):
    colors = {}
    graph = {i: [] for i in range(len(triangles))}
    for i, j in combinations(range(len(triangles)), 2):
        if incompatible(triangles[i], triangles[j]):
            graph[i].append(j)
            graph[j].append(i)
    for start in graph:
        if start in colors:
            continue
        colors[start] = 0
        todo = [start]
        while todo:
            i = todo.pop()
            for j in graph[i]:
                if j in colors:
                    if colors[j] == colors[i]:
                        return False
                else:
                    colors[j] = 1-colors[i]
                    todo.append(j)
    return True


def main():
    certificate = HERE/'overnight_upper_triangle_attachment_exact_6.json'
    data = json.loads(certificate.read_text())
    templates = [d for c, d in zip(data['coefficients'], data['descriptors']) if c != '0']
    group = probe.group(6)
    reps, counts = set(), []
    for template in templates:
        allowed = 0
        for pi in permutations(range(6)):
            descriptor = attachment.image_descriptor(template, pi)
            if two_pages([triangle for triangle, _, _ in descriptor]):
                allowed += 1
                reps.add(min(attachment.image_descriptor(descriptor, g) for g in group))
        counts.append(allowed)
    reps = sorted(reps)
    shapes = sorted({tuple(triangle for triangle, _, _ in d) for d in reps})
    print('TWO-PAGE FILTER', len(templates), 'SOURCE TYPES', counts,
          'PERMUTATION COUNTS', len(reps), 'D6 ORBITS', flush=True)
    probe.inventory = lambda n: (shapes, reps)
    with tempfile.TemporaryDirectory(prefix='max-caterpillar-two-pages-') as temp:
        probe.HERE = Path(temp)
        probe.main(6)
        record = json.loads((Path(temp)/'overnight_upper_triangle_fixed_6.json').read_text())
    record['shared_probe_sha256'] = record.pop('producer_sha256')
    record['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    record['source_certificate_sha256'] = hashlib.sha256(certificate.read_bytes()).hexdigest()
    record['source_template_count'] = len(templates)
    record['allowed_permutations_per_template'] = counts
    record['scope'] = 'Fixed cyclic order, two noncrossing pages, only the six product types in the full-S6 positive certificate. This is a subfamily of the complete two-page construction candidate. Columns average over D6 only.'
    record['status'] = record['status'].replace('FIXED_ORDER', 'TWO_PAGE_SUBFAMILY')
    (HERE/'overnight_upper_triangle_two_pages_6.json').write_text(json.dumps(record, separators=(',', ':'))+'\n')
    print('TWO-PAGE RESULT', record['status'], record['ranks'], flush=True)


if __name__ == '__main__':
    main()
