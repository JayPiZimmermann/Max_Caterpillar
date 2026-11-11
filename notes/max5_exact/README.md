# Exact Max5 width search

Active objective, 31 October 2026: determine the minimum second hidden
layer width for each first hidden layer width, with matching all-input
constructions and unrestricted lower bounds.

The model is an ordinary scalar-output ReLU network with two hidden
layers and no skips, computing the maximum of five arbitrary real inputs.
Widths count physical neurons, including signed carriers. Biases do not
change existence: homogeneous recession removes them at unchanged widths.
Positive scaling and neuron or input permutations do not change existence.

## Starting point of this search

Let m(h) be the minimum second hidden layer width at first width h,
allowing zero padding. The established unrestricted bounds are:

| First width h | Lower bound | Verified upper bound |
| --- | ---: | ---: |
| h < 9 | Impossible at every finite second width | — |
| h = 9 | 4 | 11 |
| h >= 10 | 4 | 6 |

Thus the minimum possible first width is exactly nine. Neither displayed
upper pair is claimed to have the optimal second width. The current
[source and certificate index](../../research/sN/frontier5/matching_bounds_current.md)
records the established theorem scopes.

The completed comparison-space theorem gives residual cost exactly four.
It implies second width at least six for comparison features plus one
signed carrier pair, matched by (10,6). It does not exclude arbitrary
nonroot invariant features or multiple carrier directions.

## Parallel obligations

1. The remaining (9,4) singleton-carrier branch: seven arbitrary invariant
   directions, two residual folds, all coefficient and zero-contact cases.
2. General second-width-four equality geometry, including ordinary two-core
   identities and compatible shifted translation tails.
3. Second width five with several carriers, including balanced four-core
   identities in the full comparison space.
4. Exact smaller constructions at first width nine, separating C5,
   seven-root, and nonroot dictionaries.
5. C5 four-core completion and sign-capacity bounds, with independently
   checked solver certificates and mathematical coverage.
6. Transfer of the fixed-P4 four-core exclusion to the complete sixteen-case
   root-seven catalog where valid.
7. Arbitrary-direction contact bounds, support covers, and polytope
   cancellation obstructions.
8. Primary-literature deductions and constructions with a verified bridge
   to the physical width convention above.

Every new note must distinguish a full-architecture theorem from a fixed
dictionary theorem, an exact finite necessary-condition exclusion, and a
numerical search outcome. An UNSAT report needs a model-coverage audit and
an independent proof check before promotion. A candidate network needs an
exact all-input check. No Lean implementation is requested in this search.

## Completed additions in this run

* [Mixed two-core exclusion](contact_bound.md), with
  [independent audit](contact_bound_audit.md): arbitrary nonroot first
  directions cannot produce a mixed-sign residual at physical widths
  (9,4). The proof uses the actual seven-feature span, without adding
  unprovided linear coordinates.
* [One-shared-contact exclusion](first9_nonroot.md), with
  [independent audit](one_shared_audit.md): the remaining two positive
  residual cores must share at least two four-way tie contacts.
* [C5 lower bound](first9_c5_lower.md): every pure-C5 first dictionary
  of physical width nine needs at least six second neurons, even with
  arbitrary mixtures in its four carrier rows. The
  [model audit](c5_fourcore_model_audit.md) and
  [proof index](smt_nonroot.md) separate coverage from refutation checking.
* [Nonroot construction obstructions](nonroot_search.md): two broad
  attempts to compress or lift the existing algorithms are impossible;
  this does not exclude other architectures of the same widths.
* [Local nonroot identities](triple_two_lines.md): continuous exact Max3
  families demonstrate why comparison-only normalization is not a valid
  general shortcut.
* [General negative-core lower bound](negative_core_bound.md), with
  [independent audit](negative_core_bound_audit.md): Max n requires at
  least n-2 exclusively negative residual folds over arbitrary shallow
  functions. This excludes the arbitrary-direction two-negative Max5
  case, without limiting the first width.
* [Complete invariant-hyperplane classification](polytope.md): the
  restriction of Max5 to any invariant hyperplane never has a negative
  one-core representation. Positive one-core existence has an exact
  coefficient criterion and explicit constructions.
* [Unique-positive physical width bound](unique_positive_width4.md), with
  [independent audit](unique_positive_width4_audit.md): four second
  neurons with exactly one positive output require at least fifteen
  first neurons. This does not assert attainability at (15,4).
* [Seven-root dictionary bounds](root7_k4.md): seven of sixteen catalog
  classes require at least seven physical second neurons; eight have
  an independently checked requirement of three positive corrections.

The separate Max4 component-count task has reached
[exactly 65 components at (6,5)](../berzins_max/count65_complete.md),
after positive scaling and hidden/input permutations, including biases.
The Max4 (8,4) count remains open.

The unrestricted numerical bounds at the start of this note are unchanged.
In particular, these additions do not establish an optimal Max5 width pair.
