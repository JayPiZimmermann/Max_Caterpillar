# Overnight exponential upper-construction search

Started 24 October 2026 after commit `9dbad82`. The uniform exponential exact
construction remains open. This file is the current record for this worker;
stable earlier notes are not edited.

The present discriminating test is the enlarged balanced-interval hierarchy
at seven inputs, with every canonical head root and every edge orientation.
Its all-five-state description bound is `poly(N)70^N`. A top-class identity
would imply exact face-dictionary sufficiency, but counting alone does not.

Exact enumeration gives 315 balanced trees on six nonapex labels, versus 96
in the excluded fixed hierarchy. The 219 new trees split into 84 with a
perfect matching and 135 without one. Their full dihedral unit families have
4,708 and 7,566 orbit columns respectively. The complete balanced family has
17,666 columns. This is a genuine enlargement, including all orientations;
it is not the excluded inward, single-edge, or bounded-path-shift restriction.

The first probe adds all 4,708 new perfect-matching columns to the 5,096-column
exact basis of the old hierarchy. Removing the old 296 free columns is
justified by the previously certified rational kernel identities. Thus this
9,804-column test preserves the entire old span and adds the full new
perfect-matching part. A negative result would exclude only this subfamily,
not the 7,566 new deficient columns.

Matrix generation completed in 198 seconds: 9,836 frequency rows, prime
1000000007, seed 24102561. Every entry of the first row was independently
recomputed by general-head DFS cuts. The solve gave ranks 9,682/9,683; all
122 independent rational kernel identities then passed the exact gate in
886 seconds. This is an exact obstruction to the perfect-matching subfamily,
not the complete balanced family.

The complete balanced test generated 17,402 rows for 17,370 retained columns
(the complete 17,666-column family minus the same 296 certified old
dependencies). It has modular ranks 13,146 / 13,147. All 4,224 proposed rational
null vectors reconstruct, but their exact gates have not yet passed; this is
still a modular diagnostic. The direct dense solve exceeded the 3 GiB limit,
so a controlled 6,000-pivot Schur-complement solve was used. Planted positive
and negative examples check the block elimination and lifted kernels exactly.
The complete matrix remains intact. An exact basis-shortening procedure now
records invertible row operations before attempting the large kernel gate.

A further genuine enlargement closes full BFS under the modular affine group
`x -> ax+b` on `Z/NZ`. This multiplies the description count by at most `N^2`.
At seven inputs it covers 6,216 / 9,072 apex/tree graphs and has 16,584 function
orbits. The known noncrossing witness is not contained in it. Its complete
16,616-row matrix was generated in 178 seconds by a native evaluator, checked
against 32 complete NumPy rows and an independent complete DFS row. Its block
solve is in progress. Binary linear-group closures were inventoried first:
they already cover every tree at seven and eight inputs, so their positive
span tests would not discriminate the candidate and were skipped.

Memory is kept below 3 GiB by disk-backed uint32 sample matrices and direct
row-by-row construction of FLINT matrices, avoiding large Python-int lists.
Each subprocess is restricted to one thread and at most 20 minutes. Logs and
exit receipts are produced by `overnight_upper_run.py`; generation checkpoints
can be resumed. Relevant files start `overnight_upper_`.

The existing exact seven-input noncrossing-caterpillar witness is not already
contained in these new families: 2,366 supported units lie outside balanced
trees, and 2,611 lie outside full BFS trees. Its membership cannot be inferred
from the finite positive certificate.

Parallel analytic routes retain the proved full edge-gluing factorization,
but do not reuse the refuted scalar block closure. The external apex frequency
and attachment-dependent shifts must remain in any block identity.

Broader construction branches now include noncanonical heads, unequal effective
generator lengths, subset-average features, and positive circuits. The fixed
head-set ordinary stars and three complete attached single-circuit families
fail exactly at five inputs; coordinate deletion propagates these exclusions
to every larger arity. See `overnight_upper_star_heads.md` and
`overnight_upper_circuit.md` for their exact scope. A weighted-star reopening
with apex scales 1 and 2 also fails exactly (112 columns, ranks 94 / 95,
18 exact kernel identities). These failures do not exclude arbitrary heads,
arbitrary cycles, or other exponential families. Two disjoint positive-circuit
cores joined by a mean-comparison generator are being tested next, including
the single-core terms needed for deletion closure.
