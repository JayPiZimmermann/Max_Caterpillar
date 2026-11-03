#!/usr/bin/env python3
"""Independent exact controls for the fixed-pair gate argument.

These finite tests do not prove the universal theorem. The written audit
provides that proof; this script checks boundary and signed examples using
integer arithmetic, without importing the probability worker's code.
"""
import itertools
import json
from pathlib import Path


def sign(x):
    return (x > 0) - (x < 0)


def main():
    # Three tied coordinates, four tail coordinates in two adjacent pairs.
    k, m = 3, 4
    ranks = (3, 1, 4, 2)  # anchor large; the two pair gaps are the smallest
    pairs = ((0, 1), (2, 3))
    checked = good = supported_only_selected = 0
    for w in itertools.product(range(-2, 3), repeat=k + m):
        if sum(w) or sum(v != 0 for v in w) < 3:
            continue
        checked += 1
        support = {i for i, v in enumerate(w) if v}
        if support <= set(range(k)):
            supported_only_selected += 1
            continue
        pair_count = sum(all(k + i in support for i in p) for p in pairs)
        bad = pair_count >= 2 or (pair_count >= 1 and len(support & set(range(k))) >= 2)
        if bad:
            continue
        good += 1
        base = 2 * sum(abs(v) for v in w) + 1
        gaps = [base ** r for r in ranks]
        positions = [-sum(gaps[:i + 1]) for i in range(m)]
        signs = set()
        large_coefficients = set()
        for bits in itertools.product((0, 1), repeat=len(pairs)):
            tail = list(w[k:])
            for bit, (a, b) in zip(bits, pairs):
                if bit:
                    tail[a], tail[b] = tail[b], tail[a]
            value = sum(a * b for a, b in zip(tail, positions))
            signs.add(sign(value))
            # Coefficient of gap g in the row's evaluation.
            coeffs = [-sum(tail[i:]) for i in range(m)]
            large_coefficients.add(tuple(coeffs[i] for i in range(m) if ranks[i] > len(pairs)))
            assert any(coeffs[i] for i in range(m) if ranks[i] > len(pairs))
        assert len(large_coefficients) == 1
        assert len(signs) == 1 and 0 not in signs
    result = {
        "status": "PASS",
        "scope": "Exact integer control; universal proof is in AUDIT.md",
        "selected_coordinates": k,
        "tail_coordinates": m,
        "weights": [-2, -1, 0, 1, 2],
        "zero_sum_nonbraid_rows": checked,
        "good_tail_supported_rows": good,
        "selected_only_rows": supported_only_selected,
        "pair_orientations_per_row": 4,
    }
    Path(__file__).with_name("control.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
