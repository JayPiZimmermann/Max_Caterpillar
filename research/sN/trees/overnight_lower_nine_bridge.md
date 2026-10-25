# Nine-label separation and a uniform fifth-degree all-tree bound

25 October 2026. **Certified by complete exact arithmetic and independent
replay; counting bridge independently reviewed.** All 1,971 rows passed two
exact evaluation algorithms. A separate 115.19-second streaming check replayed
every kernel relation, every modular reduction, and complete row coverage;
its status is `INDEPENDENT_COMPLETE_N9_EXACT_RANK_CERTIFICATE_PASS`.
This proves the uniform polynomial bound below, not the requested exponential
theorem or a matching nine-input network width.

## Finite separation gate

At arity nine, consider every canonical rooted, oriented tree unit whose
tree on the eight nonapex labels has no perfect matching. Full permutation
sums have 3,822 normalized function orbits. An independent complete tree
inventory and an independent subset-recurrence checker cover this domain.
Missing or linearized edges already put a face function in L_7.

The finite evaluation matrix has 1,971 rows. Exact evaluation by
two different arithmetic algorithms checked 1,852 independent column
relations: each has its own nonpivot column with coefficient one, and all
other entries lie in the same 1,970 pivot columns. Thus the ordinary rational rank is at most 1,970.
A separate scalar elimination
checks the augmented minor modulo 1,000,003, with determinant 938,220.
Every rational row is also checked to reduce to its modular row with
nonzero denominator. Hence augmented rational rank is at least 1,971.

This separates the maximum from all the ordinary columns over Q and R.
The generic Fourier transform annihilates L_7. Permutation averaging any
hypothetical representation of the symmetric maximum therefore proves
separation from the entire canonical family, including every apex label,
head root, and edge orientation. No characteristic-zero conclusion is drawn
from a modular rank gap alone.

## Counting consequence

The finite gate has passed. For N>=9, any exact expansion of max_N in canonical
tree face functions and the auxiliary shallow span uses at least

    binom(N,5)/126

terms. In fact this lower bound counts only terms whose ORIGINAL nonapex
tree has matching number at least four. Arbitrarily many other canonical
tree terms can be adjoined for free.

At each nine-label top tie, put all other coordinates at distinct negative
superincreasing values. The existing canonical head-flow reduction says
that a contributing term must retain its apex; its other eight tied labels
induce a connected original subtree, all whose internal edges are hinges.
The local top germ is another canonical tree unit. The finite separator
therefore forces at least one term whose induced eight-vertex subtree has
a perfect matching.

A forest has at most one perfect matching: the symmetric difference of
two would contain an alternating cycle. Sending such an induced subtree
to its four matching edges is consequently injective, since the union of
their endpoints recovers the entire eight-vertex set. For a fixed original
unit the apex is fixed too, so its number of covered nine-label ties is at
most the number of four-edge matchings of its (N-1)-vertex tree.

A forest on n vertices has at most binom(n-k,k) matchings of size k.
For completeness, induct on n. If there is an isolated vertex, deleting it
preserves the count and decreases the displayed upper bound. Otherwise
choose a leaf v with neighbor w. A k-matching either avoids vw or contains
it, giving the recurrence bound

    binom(n-k-1,k) + binom(n-k-1,k-1) = binom(n-k,k).

The cases k=0 and n<2k are immediate. Thus one original unit covers at most
binom(N-5,4) ties. Covering all binom(N,9) nine-label ties yields

    |K| >= binom(N,9)/binom(N-5,4) = binom(N,5)/126.

If its original matching number is at most three, a unit covers none of
these ties and is not counted. All orientations and face states remain
allowed throughout. Weighted real heads and independently weighted tree
edges are outside this canonical theorem.

## Evidence and publication scope

The campaign sources, independent inventory, independent recurrence
semantics, two exact arithmetic engines, modular minor checker, and final
streaming checker are documented in `overnight_lower_exact9_README.md`.
Large reproducible rational rows are local caches, with content hashes and
small receipts retained. The final streaming checker replays every exact
column relation and modular reduction and verifies complete row coverage.

This note is research-only. Small-input network width results are kept out
of the paper; the nine-label computation here proves a uniform all-arity
bound, not an optimal small-input network result. Neither the finite separator nor its counting
bridge has been formalized in Lean.
