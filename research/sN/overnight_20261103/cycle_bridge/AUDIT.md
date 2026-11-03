# Independent semantic audit of the actual cycle-to-forest bridge

The audit reads the primitive network definitions and the new construction;
it does not infer semantics from theorem names. The independent driver is
`Check.lean`. The exact claim is equality of two finite **representability
classes**, with widths allowed to change. Because translation normalization
fixes the output's diagonal slope to one, these classes are not themselves
asserted to be vector spaces.

## Construction and scope

`NetworkExpansion.exists_expansion` starts from an actual
`NormalizedNetwork N h₁ h₂` with zero-sum first-hidden rows and second-hidden
linear heads, output linear slope one, and first-hidden support at most two.
The source has arbitrary signed real coefficients and braid output skips.
No forest, matching, generic-position, rationality, or decomposition premise
is supplied by the caller.

The original-neuron decomposition chooses one finite coefficient family for
all real inputs simultaneously. The indexed replacement uses one first-hidden
row for each unordered coordinate pair and a finite dependent family of
second-hidden slots. `FiniteIndex.indexedNetwork` reindexes those families as
literal `Fin` arrays, including empty families. Linearized cycle terms enter
the second-hidden linear heads; the canonicalization of the original shallow
output is retained in the new output skip and linear head. Normalization and
equality of the complete output are proved from these arrays.

The actual summed signed interaction graph of each new neuron is a subgraph
of its forest-state graph and of one original neuron's graph. This keeps
parallel-row cancellation in the definition of the original graph. The
argument never substitutes a union of raw first-hidden supports for that
graph. Graph deletion preserves the matching bound, and the finite forest
cover theorem gives a cover with at most the old matching bound.

The exact second-hidden width bound is

    new_h₂ ≤ old_h₂ * 3 ^ Fintype.card (ActualBraid.Pair N).

This is not a width-preserving transformation and cannot, by itself, carry a
quantitative lower bound on forest networks back to the original width.

## Obstruction equivalence

`Equivalence.localMatchingObstruction_iff_no_cover_representation` identifies
the existing `LocalMatchingObstruction N (r+1)` with exclusion of actual
normalized braid networks computing `Maximum N` whose individual interaction
graphs all have vertex covers of size at most `r`. Input arity is unchanged.
The proof does not establish either obstruction at a new parameter value.

`Check.exact_obstruction_contract` unfolds the cover condition into ordinary
endpoint membership and quantifies explicitly over finite network widths,
the network, its normalization, the all-real-input MAX identity, and each
second-hidden slot. `MatchingCoverCheck.lean` separately unfolds the matching
condition into an edge subset, edge count, and pairwise endpoint disjointness.

## Nonvacuity and boundary controls

The driver constructs an actual three-input network with three comparison
rows, coefficient one on every edge of a triangle, and one second-hidden
neuron. Its original interaction graph is the complete three-vertex graph
and is not acyclic. Its zero-sum head is chosen so that the outer preactivation
takes values -1 and 3 at two explicit inputs, so this control also has a
genuine changing outer gate. Applying the replacement theorem produces an actual
finite network with forest interaction graphs computing exactly the same
function at every real input. This control is deliberately a same-function
test; it is not presented as a one-neuron MAX₃ construction.

A separate one-input control uses empty first and second hidden layers and
computes MAX₁ with its linear output. It supplies a cover-zero representation
and proves that `LocalMatchingObstruction 1 1` is false. The general equivalence
therefore is not being checked only on an inconsistent structural premise.

## Evidence boundary

The new exact-type drivers and their axiom reports must pass in the enclosing
content-bound build before publication. No proof gap was found in the source
audit. An audit of this reduction is not a proof of a growing-arity structural
obstruction or an unconditional exponential width bound.
