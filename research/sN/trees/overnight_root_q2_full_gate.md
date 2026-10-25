# Full mixed nine-label diagnostic for the existing Q2 score

25 October 2026. This does not establish or refute descent of Q2.

The old gate covered perfectly matchable shapes and stars. The new bounded
gate uses every one of the 5450 normalized canonical function classes and
the maximum, retaining the same fixed Q2 formula and target value -1/810.
It adds 1288 modular frequency rows to the old 2112-row inventory, with
prime 1000003. The resulting evaluation rank is 2476, and the score row
does not belong to that sampled row space. There are 553 violated sampled
kernel vectors; the smallest reconstructed proposal has sixteen terms,
coefficients +/-1, and exact Q2 pairing -588.

None of these facts is an exact functional refutation. An evaluation-kernel
vector must first be proved to be a rational identity, or a whole-function
identity modulo the permitted lower-dimensional span. Rank stabilization
and many successful sampled checks do not prove that identity.

The sixteen-term proposal is in `overnight_root_q2_relation16.txt`.
Both existing chamber-aggregation methods reject it as a zero WHOLE
FUNCTION: the C++ coordinate implementation finds 2605 nonzero mixed walls,
and the independent Python gap implementation confirms the same 2605
nonzero wall coefficients. The same exact chamber gate rejects each of the twelve shortest
proposals. Their results are retained in
`overnight_root_q2_function_proposals.json`. This does not exclude an
identity of generic Fourier kernels: a nonzero function may belong to the
lower-dimensional span.

At a fresh modular frequency point, the sixteen-term proposal vanishes
separately in each actual-apex sector. This suggests looking for a fixed-
apex identity, but remains a necessary diagnostic. An exploratory exact
single-residue dictionary calculation cancels several pole types literally;
other types retain nonempty fraction dictionaries. No common-denominator
proof for the latter has been completed.

Two concrete next certification routes are available: a complete rational
residue/circuit reduction, or identification as a substitution of a smaller
fixed-apex relation, with arbitrary attached rooted trees. Neither bridge
is supplied here. The six-term local graft identities already checked in
`overnight_uniform_fay.md` are not a complete presentation theorem.

The producer is `overnight_root_q2_full_gate.py`. It uses the existing q9
inventory and native DP evaluator, writes only its own prefix, runs on one
thread with a 3-GiB address-space limit, and finished the 3400-row gate in
88.3 seconds. Its new raw evaluation matrix remains a local generated
cache. The finite gate receipt is
`overnight_root_q2_full_gate_3400.json`. Q2 remains an unproved candidate;
the unrestricted exponential lower bound is unchanged.
