"""Independent exact subset-sum check of the MAX finite-difference identity.

No proof helpers or enumeration conventions are imported from the Lean
producer. Positive unequal increments, ties, range-one boundaries and
diagonal-annihilator failure are included. Budget: n<=5, 60 seconds.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json
import time

HERE = Path(__file__).resolve().parent
start = time.monotonic()
VALUES = (Fraction(-2), Fraction(-1, 2), Fraction(0), Fraction(1))


def difference(x, increments):
    n = len(x)
    total = 0
    for mask in range(1 << n):
        shifted = [x[i] + (increments[i] if mask >> i & 1 else 0) for i in range(n)]
        total += (-1) ** (n - mask.bit_count()) * max(shifted)
    return total


results = []
for n in range(1, 6):
    checks = 0
    for x in product(VALUES, repeat=n):
        for a in [(Fraction(1),) * n,
                  tuple(Fraction(i + 1, i + 2) for i in range(n))]:
            expected = (-1) ** (n - 1) * max(0, min(t + u for t, u in zip(x, a)) - max(x))
            assert difference(x, a) == expected
            checks += 1
    assert difference((Fraction(0),) * n, (Fraction(1),) * n) == (-1) ** (n - 1)
    if n >= 2:
        assert difference((Fraction(1),) + (Fraction(0),) * (n - 1),
                          (Fraction(1),) * n) == 0
    results.append({'n': n, 'exact_input_increment_checks': checks})

# The general unequal-increment statement needs positive increments.
assert difference((Fraction(0), Fraction(0)), (Fraction(-1), Fraction(-1))) == -1
# A repeated diagonal translation DOES annihilate MAX. This is outside
# the theorem's explicitly checked non-diagonal-period hypothesis.
def translate(x, v):
    return tuple(a + b for a, b in zip(x, v))

for n in range(2, 6):
    v = (Fraction(1),) * n
    for x in product(VALUES, repeat=n):
        assert max(translate(translate(x, v), v)) - 2 * max(translate(x, v)) + max(x) == 0

assert time.monotonic() - start < 60
report = {
    'status': 'PASS', 'evidence_kind': 'Independent exact finite controls, not a substitute for the all-real Lean proof.',
    'results': results, 'total': sum(r['exact_input_increment_checks'] for r in results),
    'negative_controls': ['Nonpositive unequal increments need not satisfy the claimed positive-increment formula.',
                          'Two repeated diagonal differences annihilate MAX, so the non-diagonal condition is substantive.'],
    'elapsed_seconds': time.monotonic() - start,
    'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
(HERE / 'tent_control_result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
