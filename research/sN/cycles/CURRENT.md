# Cyclic-graph construction DFS, 24 October 2026

Target: an explicit O(C^N) family of second-hidden-layer units whose span,
together with all exposed-face functions and linear functions, contains max_N.
A fixed cycle on the N-1 nonapex labels, arbitrary edge orientations and states,
is the first candidate. A self-loop gives sigma(0)=0; "loops" here means cycles.

Budget: first validate the general-head tree Fourier formula against a separately
implemented braid-chamber integral on exact rational frequencies, N=4,5.
Then test fixed-cycle families at increasing N using dihedral orbit sums and
modular ranks, at most 180 seconds per arity. Modular rank gaps are diagnostics,
not characteristic-zero impossibility proofs. Seed 24102411, prime 1000003.

The full-cycle zonotope tiles into its N-1 path zonotopes by projecting the unit
cube along its diagonal and selecting the representative with minimum coordinate
zero. The cone over the tiling gives a top-class identity. This converts cyclic
units into tree atoms with translated integer heads, not necessarily canonical
heads x_root-x_apex. The unrestricted tree lower-bound conjecture therefore
cannot simply be applied to these atoms. This experiment keeps the apex outside
the graph; it does not cover cycles through the apex or arbitrary signed inner
coefficients.

## First decisive result

The full fixed-cycle family already fails at N=5. There are 1040 distinct
units and 106 dihedral orbit sums. The exact checker proves 32 independent
rational-function relations, so the characteristic-zero rank is at most 74;
recomputed finite-field evaluations give augmented rank 75. Thus max_5 is not
in this family's top-class span, even after adding all faces. Receipt:
`cycle_obstruction_5.json`; producer `cycle_exact.py 5`; 19.6 seconds.
The 16 exact rational controls in `controls.json` independently compare tree
and cycle formulas with chamber integrals; they are controls, not a uniform
proof by sampling. The tiling and coordinate-change proofs supply that bridge.

Next branch (budget 240 s, prime1000003, seed24102412): enlarge the old fixed-
circle noncrossing caterpillar family by every source/root marking of every
noncrossing Hamiltonian path, including short marked paths. This keeps an
exponential-size candidate and directly relaxes the recorded NC8 obstruction.
First test N=8, all orbit columns plus30 frequency rows. No modular positive
or negative result is promoted without an exact gate.

The first marked-path run reached its180-second generation budget before the
first1000-row progress report. This is an instrument timeout, not a rank result.
A measured FLINT setter control takes0.69s per200,000 entries; the revised run
logs each phase and100rows, saves family metadata before evaluation, and allows
420s for generation plus60s for elimination. It preserves the initial log as
`nc_marked_paths_8_budget180.log`. If that budget expires, retain the precise
completed-row count and leave the mathematical question open.

The instrument's second attempt stopped at3722 of5543rows after420s. The
third attempt uses32-frequency vector batches and a disk-backed uint32 row
cache, checkpointed after each batch. It reuses the exact family metadata and
the same deterministic points; producer `nc_marked_batch.py`,480s budget.
The row cache is ignored by Git and can be regenerated. Initial measured
throughput is about32rows/s versus10rows/s before batching.

A concurrent cleanup moved OneBasis.lean to Retained.lean and put the short
rational-projection proof directly in Rationality.lean. The paper's affected
links were updated to the surviving declarations; obsolete version-history
claims were replaced by the current proof routes. No production Lean file
was changed by this continuation. The earlier122-statement receipt is now
historical until the concurrent cleanup regenerates it; do not treat its
source hashes as a certificate of this changing working tree.

A viable larger target permits every noncrossing graph, including cycles, on
the nonapex labels. It has at most N^2*100^N descriptions after all face states
are included (triangulation count times five states per edge). A uniform top-
class identity for that family would therefore give a genuinely exponential
exact construction by the already proved face-closure lemma. Sufficiency is
OPEN; the count alone is not an upper construction. See `PROOFS.md`.

## Completed larger tree probe

The batched run finished in248.7s: old NC caterpillars plus every source/root
marking of every noncrossing Hamiltonian path at N=8 gives87,920 units,
5,513 dihedral orbits, and5,543 frequency equations. The modular ranks are
5,315/5,316. This is another negative diagnostic, NOT an exact real-span
obstruction;198 right-kernel proposals have been saved for a possible exact
gate. Neither arbitrary noncrossing trees nor noncrossing cyclic graphs have
been excluded. All numerical rows are reproducible from the metadata and seed;
`nc_marked_check.py` separately rebuilds250 cut lists by graph traversal and
recomputes one complete evaluation row using scalar arithmetic.

Paper update: broader certified out-leaf scope and the arbitrary-shape,
full-hinge source/root example are now in `paper/main.tex`. PDF36pages; final
LaTeX log has no overfull boxes, undefined references, or warnings. The link
checker resolves182 declarations after the concurrent source-file moves.

The batch producer wrote its complete result and DONE log, but the tool session
subsequently reported exit143. A separate clean replay loaded the cached rows
and recomputed ranks5315/5316 in33.8s; `nc_marked_rank_recheck.json` and its log
are the final rank receipt. The independent graph-traversal/scalar-row controls
also pass. This extra replay verifies the recorded numeric result despite the
producer session's nonzero termination status.

The paper now also includes the sharper7/6 bound for full-hinge source/root
units on arbitrary tree shapes, with its covering-forest proof at the end of
the count appendix. This mathematical bridge is reviewed but not yet a Lean
declaration. The generic out-leaf theorem cited earlier is Lean certified.

Final paper prose review found and corrected one quantifier: the singleton
cover condition concerns isolated vertices of R **in Phi**, not the apex or
deleted pendants. Leaves were also separated explicitly in the degree count.
The final proof preserves the independently reviewed mathematical claim.

The concurrent cleanup subsequently consolidated the count proof into
`MaxCaterpillar/Count/{Locality,Passing,PerUnit,Classes,Main}.lean` and moved
the dimension proof to `MaxCaterpillar/Dimension.lean`. Paper links now use
these surviving declarations; unused mappings to removed routes were deleted.
The out-leaf paragraph now states the sharper bound
`(1+1/(2s+4))^N/(N+1)` supplied by `Count.outLeaf_unified_exponential`.
The final link inventory has175 entries. These moved modules are still part
of the concurrent cleanup; its fresh global Lean gate remains separate.

## Published checkpoint and arbitrary-orientation continuation

The checkpoint and prior local commits were pushed through `9147823`.
Paper Lean links are pinned to source snapshot `039d684`. The subsequent
[orientation continuation](../trees/ORIENTATIONS.md) proves a matching-based
exponential bound with all orientations and all face states, and propagates
the five-label separator to allow all oriented stars. The unrestricted
all-tree theorem and exponential upper construction remain open. The paper
now includes these mathematical extensions; they are not Lean declarations.
The public theorem interface builds, but the complete historical manifest
still needs reconciliation after the cleanup.
