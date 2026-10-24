#!/usr/bin/env python3
"""Check every proposed Fourier relation needed for an ordinary rank upper bound.

The independent free coordinates prove linear independence of the relations.
The augmented rank lower bound is supplied by the separately reproducible
modular producer; this script does not replace its matrix calculation.
Budget 180 s per invocation; successful relation indices are checkpointed.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys
import time

from exponential_families_probe import exact_expression
from rational_identity import add, Verifier

HERE = Path(__file__).parent


def main(n, mode, restriction):
    source = HERE / f'exponential_batch_{mode}_{restriction}_{n}.json'
    dest = HERE / f'exponential_kernel_{mode}_{restriction}_{n}.json'
    data = json.loads(source.read_text())
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    free = data['kernel_free_columns']
    proposals = data['kernel_proposals']
    assert len(free) == len(proposals) == len(set(free))
    assert all(v is not None for v in proposals)
    for f, raw in zip(free, proposals):
        vector = {int(j): Q(v) for j, v in raw}
        assert len(vector) == len(raw)
        assert [vector.get(j, Q(0)) for j in free] == [Q(j == f) for j in free]
    passed = []
    if dest.exists():
        old = json.loads(dest.read_text())
        if old['source_sha256'] == source_hash:
            passed = old['passed_indices']
    verifier = Verifier(budget=180)
    result = dict(n=n, family=mode, orientation_restriction=restriction,
                  source=source.name, source_sha256=source_hash,
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  independent_relations=len(free), passed_indices=passed,
                  ordinary_rank_upper=data['orbit_count'] - len(free),
                  augmented_rank_lower_from_modular_receipt=data['ranks'][1],
                  status='EXACT_KERNEL_CHECK_PENDING', budget_seconds=180)
    forms = [tuple(int(i == j) for i in range(n - 1)) + (0,) for j in range(n - 1)]
    forms.append((-1,) * (n - 1) + (0,))
    one = (0,) * (n - 1) + (1,)
    for j, raw in enumerate(proposals):
        if j in passed:
            continue
        expression = exact_expression(n, [data['orbits'][i] for i, value in raw], [Q(value) for i, value in raw])
        # exact_expression subtracts the simplex; kernel identities do not.
        add(expression, (-1) ** (n - 1), one, 0, [(f, 1) for f in forms])
        try:
            ok = verifier.check(expression)
        except TimeoutError:
            result['status'] = 'EXACT_KERNEL_BUDGET_REACHED_NO_CONCLUSION'
            break
        if not ok:
            result.update(status='KERNEL_PROPOSAL_FAILED', failed_index=j)
            break
        passed.append(j)
        if len(passed) % 20 == 0:
            print('VERIFIED', len(passed), '/', len(proposals), 'SECONDS', round(time.time() - verifier.start, 2), flush=True)
            dest.write_text(json.dumps(result, indent=2) + '\n')
    if len(passed) == len(proposals):
        assert result['ordinary_rank_upper'] < result['augmented_rank_lower_from_modular_receipt']
        result['status'] = 'ALL_EXACT_KERNEL_IDENTITIES_VERIFIED'
    result.update(symbolic_calls_this_run=verifier.calls, seconds_this_run=time.time() - verifier.start)
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print('DONE', result['status'], len(passed), '/', len(proposals), 'SECONDS', result['seconds_this_run'], flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 'full')
