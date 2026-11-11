"""Independent omission-only support cover for the selected six classes.

No imported producer, SMT solver, old cover, or mathematical UNSAT claim.
The local MAX4 rigidity implication is a separate written dependency.
"""
from collections import Counter
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, product
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
TASK = HERE.parent
ROOTS = ((0, 2), (1, 2), (3, 4))
EXPECTED = {
    275: ((0, 1, 2), (0, 1, 3), (0, 1, 3), (0, 1, 4)),
    277: ((0, 1, 2), (0, 1, 3), (0, 1, 3, 4), (0, 1, 4)),
    280: ((0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 3, 4)),
    307: ((0, 1, 2, 3), (0, 1, 3), (0, 1, 4), (0, 1, 4)),
    353: ((0, 1, 3), (0, 1, 3), (0, 1, 4), (0, 1, 4)),
    355: ((0, 1, 3), (0, 1, 3), (0, 1, 4), (0, 2, 4)),
}

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def permutations():
    result = []
    for swap_unique, swap_shared in product((False, True), repeat=2):
        p = list(range(5))
        if swap_unique:
            p[0], p[1] = p[1], p[0]
        if swap_shared:
            p[3], p[4] = p[4], p[3]
        result.append(p)
    return result

def canonical(rows):
    return min(tuple(sorted(tuple(sorted(p[i] for i in row)) for row in rows))
               for p in permutations())

def has_c3_c4(rows):
    supports = [set(s) for s in ROOTS + tuple(rows)]
    return (all(any(s <= set(I) for s in supports)
                for I in combinations(range(5), 3))
            and all(any(a in s and s <= set(I) for s in supports)
                    for I in combinations(range(5), 4) for a in I))

def main():
    types = [tuple(s) for n in (3, 4, 5) for s in combinations(range(5), n)]
    counts = Counter()
    survivors = []
    examined = 0
    for rows in combinations_with_replacement(types, 4):
        examined += 1
        if all(sum(i not in s for s in rows) >= minimum
               for i, minimum in ((2, 3), (3, 2), (4, 2))):
            survivors.append(rows)
            counts[canonical(rows)] += 1
    assert len(types) == 16 and examined == 3876
    assert len(survivors) == 12
    assert set(counts) == set(EXPECTED.values())
    assert [counts[EXPECTED[i]] for i in EXPECTED] == [2, 1, 2, 2, 1, 4]
    assert all(has_c3_c4(rows) for rows in survivors)
    metadata_hashes = {}
    for index, expected in EXPECTED.items():
        name = f'case{index}' + ('_single' if index == 277 else '')
        path = TASK / (name + '.metadata.json')
        data = json.loads(path.read_text())
        assert data['index'] == index
        assert tuple(map(tuple, data['mandatory_roots'])) == ROOTS
        remaining = list(map(tuple, data['supports']))
        for root in ROOTS:
            remaining.remove(root)
        assert tuple(sorted(remaining)) == expected
        metadata_hashes[path.name] = digest(path)
    receipt = {
        'status': 'INDEPENDENT_OMISSION_ONLY_SIX_CASE_COVER_PASS',
        'scope': 'Complete support cover for exactly three physical roots in the declared same-label contact sector; no arithmetic UNSAT or Lean claim.',
        'support_types': len(types), 'multisets_examined': examined,
        'labelled_survivors': len(survivors), 'support_orbits': len(counts),
        'c3_c4_redundant_on_all_survivors': True,
        'cases': [{'index': i, 'supports': r, 'orbit_size': counts[r]}
                  for i, r in EXPECTED.items()],
        'selected_metadata_sha256': metadata_hashes,
        'checker_sha256': digest(__file__),
        'argument_sha256': digest(HERE / 'MINIMAL_COVER.md'),
    }
    (HERE / 'minimal_cover_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in (
        'status', 'multisets_examined', 'labelled_survivors', 'support_orbits',
        'c3_c4_redundant_on_all_survivors')}))

if __name__ == '__main__':
    main()
