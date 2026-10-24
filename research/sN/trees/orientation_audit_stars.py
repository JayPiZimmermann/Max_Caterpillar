#!/usr/bin/env python3
"""Exact vertex controls for uniform arbitrary-orientation star deletion.

Budget 90 seconds. Canonical apex=0, centre=1 (label equivariance); all
roots, orientations, and coordinate deletions for m=5..9. The checks use
exposed vertices directly, not Fourier formulas or sampled evaluations.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent


def add(x, y):
    return tuple(a+b for a, b in zip(x, y))


def basis(m, j):
    return tuple(int(i == j) for i in range(m))


def delta(m, a, b):
    return tuple(int(i == a)-int(i == b) for i in range(m))


def zonotope(head, gens):
    out = {head}
    for gen in gens:
        out |= {add(x, gen) for x in out}
    return out


def project(x, j):
    return x[:j] + x[j+1:]


def main():
    start = time.monotonic()
    cases = {}
    per_arity = []
    total = 0
    for m in range(5, 10):
        before = total
        zero = (0,) * m
        for root in range(1, m):
            head = delta(m, root, 0)
            for bits in itertools.product((-1, 1), repeat=m-2):
                gens = [tuple(s*z for z in delta(m, leaf, 1))
                        for leaf, s in zip(range(2, m), bits)]
                Z = zonotope(head, gens)
                Q = Z | {zero}
                for j in range(m):
                    assert time.monotonic()-start < 90, "90-second budget exhausted"
                    lo, hi = min(x[j] for x in Q), max(x[j] for x in Q)
                    Qlo = {project(x, j) for x in Q if x[j] == lo}
                    Qhi = {project(x, j) for x in Q if x[j] == hi}
                    zero1 = (0,) * (m-1)
                    if j == 0:
                        tag = "apex_zonotope_minus_zero"
                        assert Qlo == {project(x, j) for x in Z}
                        assert Qhi == {zero1}
                    elif j == 1:
                        tag = "centre_difference_of_segments"
                        assert len(Qlo) <= 2 and len(Qhi) <= 2
                    else:
                        sign = bits[j-2]
                        kept = [g for i, g in enumerate(gens) if i != j-2]
                        Z0 = zonotope(head, kept)
                        Z1 = {add(x, gens[j-2]) for x in Z0}
                        proj0 = {project(x, j) for x in Z0}
                        proj1 = {project(x, j) for x in Z1}
                        if j != root and sign == 1:
                            tag = "nonroot_outward_positive_star"
                            assert Qlo == proj0 | {zero1}
                            assert Qhi == proj1
                        elif j != root and sign == -1:
                            tag = "nonroot_inward_negative_star"
                            assert Qlo == proj1
                            assert Qhi == proj0 | {zero1}
                        elif sign == 1:
                            tag = "root_outward_negative_zonotope"
                            assert Qlo == {zero1}
                            assert Qhi == proj1
                        else:
                            tag = "root_inward_transfer_to_centre"
                            assert Qlo == proj1 | {zero1}
                            assert Qhi == proj0
                            new_head = project(delta(m, 1, 0), j)
                            new_gens = [project(g, j) for g in kept]
                            assert proj1 == zonotope(new_head, new_gens)
                    cases[tag] = cases.get(tag, 0) + 1
                    total += 1
        # Independent direct check of T_j max_m = max_(m-1).
        simplex = {basis(m, j) for j in range(m)}
        for j in range(m):
            lower = {project(x, j) for x in simplex if x[j] == 0}
            upper = {project(x, j) for x in simplex if x[j] == 1}
            assert lower == {basis(m-1, i) for i in range(m-1)}
            assert upper == {(0,) * (m-1)}
        per_arity.append({"m": m, "deletion_cases": total-before})
        print("checked", m, total-before, "cases", round(time.monotonic()-start, 3), flush=True)
    constants = 0
    for N in range(5, 501):
        # Multiply the polynomial absorption inequality by 11^4*13.
        weighted_p4 = sum(math.comb(N,j) * 2**j * 11**(4-j) for j in range(5))
        coeff = 13*weighted_p4 + 13*11**4*(N-4) + 2*(N-1)*11**4
        assert coeff <= 13*11**4*(N+1)**4
        assert (1 << N)-sum(math.comb(N,j) for j in range(5)) >= 1 << (N-5)
        constants += 1
    report = {
        "status": "EXACT_VERTEX_DELETION_CONTROLS_PASS_NOT_A_LEAN_PROOF",
        "domain": "m=5..9, apex 0 and centre 1 by label equivariance; all roots, orientations, deletions",
        "deletion_cases": total,
        "cases": cases,
        "per_arity": per_arity,
        "finite_constant_instances": constants,
        "budget_seconds": 90,
        "elapsed_seconds": time.monotonic()-start,
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "base_certificate_sha256": hashlib.sha256((HERE/'all_tree_dfs/complete_flags_5.json').read_bytes()).hexdigest(),
        "base_independent_checker_sha256": hashlib.sha256((HERE/'dfs_review_flag_certificate.py').read_bytes()).hexdigest(),
    }
    (HERE/'orientation_audit_stars.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
