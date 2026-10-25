# Overnight proof search: morning checkpoint, 25 October 2026

The unrestricted canonical all-tree exponential lower bound and a uniform
exact construction of size 2^{O(N)} remain open. The paper's construction
still has size 2^{O(N log N)}. The search continued through the night;
proved statements, exact counterexamples and unresolved solver runs are
kept separate below. Unmatched small-input results remain research-only.

## Bounds and constructions currently established

| Model | Established result | What is not asserted |
|---|---|---|
| Canonical tree face dictionary, all shapes, roots, apices and orientations | For N>=9, at least binom(N,5)/126 terms whose original tree has matching number at least four | This is polynomial; arbitrary weighted heads/edges are not covered by this unrestricted-tree statement |
| The original caterpillar and specified related-paper dictionaries, mixed with weighted bounded-degree/bounded-excess graph families | The previously proved exponential bounds remain valid; canonical matching-number-at-most-three trees can be added for free | No exponential bound for unrestricted weighted trees |
| Five inputs, arbitrary first hidden layer and any finite second hidden layer | Minimum first hidden layer width is 9, attained by the exact (9,14) network | Fourteen is not proved optimal |
| The prescribed ten-row first hidden layer | Minimum second hidden layer width is exactly 6 | This does not impose a lower bound of 6 on all first layers |
| The complete sixteen-row comparison first hidden layer | Second hidden layer width is between 5 and 6 | No (16,5) construction or exclusion yet |
| The specific nine-row P4 first hidden layer | Second hidden layer width is between 7 and 14 | This is not a statement about every first layer of width 9 |
| Five inputs, arbitrary first hidden layer and width | Minimum second hidden layer width remains between 4 and 6 | Strict dependence of the unrestricted minimum h2 on h1 is unresolved |

The two matched five-input statements are already in the paper. No
unmatched small-input search result was added. The last paper build has
46 pages and passed its reference/overflow checks.

The all-tree polynomial bound rests on the completed exact nine-label
certificate, not a numerical rank estimate. Its independent streaming
replay checked all 3,650,292 rational column-relation entries. See
[the certificate instructions](trees/overnight_lower_exact9_README.md),
[the counting bridge](trees/overnight_lower_nine_bridge.md), and
[the free matching-number-three extension](trees/overnight_free_matching3.md).

## What makes the unrestricted tree bound difficult

A score assigned to a tree description is insufficient. Different roots,
apices and orientations can describe functions satisfying exact linear
relations, and a valid lower-bound functional must respect every such
relation. Signed coefficients also prevent a simple positive covering
argument. Several plausible matching and residue scores fail these tests.

The counting half is ready: a uniform functional killing units with two
nonroot outward leaves at one hub would imply Omega((2/phi)^N), without
a polynomial loss. The analytic functional is still missing. This is a
conditional reduction, not the claimed exponential lower bound; see
[the Fibonacci counting proof](trees/overnight_uniform_twin_dp.md).

The strongest current structural route isolates nonsingleton shifted-minus
cuts by their actual apex. Their residues factor into smaller marked
kernels. Relations retaining the attachment marks lift exactly, and a
root-slide defect has an explicit triangular correction. What remains is
a presentation theorem controlling relations that move those marks while
preserving the required annihilated span. See
[marked cut lifts](trees/overnight_uniform_cut_presentation.md) and
[matching states and divided differences](trees/overnight_uniform_cut_matching.md).
The recorded endpoint ranks are diagnostics, not that presentation theorem.

The leaf-double-wheel injectivity shortcut fails by an independently
checked seven-label witness. Scalar torsion traces and raw matching
signatures also fail. These closed routes and their precise counterexamples
are retained so later searches do not repeat them.

## What remains viable for an exponential construction

The live geometric candidate is a family of sparse cyclic graphs: a full
star together with a pair of twin binary-search trees, allowing all five
edge states and global input reflection. Its description count is
exponential. Exact five-input and seven-input controls show positive
top-class containment, but do not establish an all-arity network identity.

There is now a uniform positive closure lemma for N>=3: every head-subset state of
a contained spanning tree stays in the reflected five-state graph family.
Centering the head mark has exact lower-dimensional corrections, at most
2^(N-1) for one operation. See
[the head-motion lemma](trees/overnight_upper_head_gauge.md).
This is a whole-function identity. It does not bound accumulated width
under iteration or prove product/coproduct compatibility.

Conversely, assigning one sparse graph to each Baxter class cannot work.
The ascending class requires all binom(N-2,2) comparisons among its middle
labels, even with arbitrary real heads, signed weights and a lower-dimensional
remainder. Thus any successful construction must mix graphs or classes.
The proof uses explicit directional flags, with an independent evaluator
on the original nested ReLUs; see
[the uniform class obstruction](trees/overnight_upper_hopf_dense_class.md).

Formal logarithmic head transfer and the marked Eulerian/Bernoulli identity
are exact, but generic finite truncation fails after coning. They are
algebraic tools awaiting a geometric map, not compact network constructions.

## The new exact five-input search domain

For N>=5, a sum of two outer ReLUs over the complete comparison span cannot
represent max_N modulo a shallow remainder. The new proof is short:
locality at a top-three tie, propagation across braid chambers, and a
third finite difference of a Boolean quadratic. The old finite certificate
is preserved. With three cores, the same argument proves that every
interior cancellation is pairwise. See
[the uniform proof](best5/overnight_fixed_complete_uniform_mixed.md).

This makes the five-input formulation complete: 42 unrestricted real
parameters, both mixed output-sign counts, all 120 braid cones, and all
weak/zero cases. Sparse complement coordinates and exact quadruple-tie
covers provide smaller equivalent descriptions. Bounded Z3 and cvc5
runs, including the closed cover campaign, did not decide the full problem.
Timeouts imply no lower bound.

One restricted obstruction is certified: retaining the negative core of
the known (10,6) network up to scaling, sign and input relabeling cannot
work with only two otherwise free positive cores and a shallow remainder.
Ethos independently checked a cvc5 proof against the exact input formula.
The solver is not required for replay; see
[the statement and replay instructions](best5/overnight_root_complete_ethos.md).
This does not exclude a different three-core construction.

## Verification and next steps

Frozen manifests record sources, dependencies and hashes. Independent
checks use exact arithmetic, direct directional jets, complete cone
verification, or an external proof checker as appropriate. The historical
public Lean certificate still checks 122 statements dated 24 October.
The newer geometric arguments are written proofs with separately identified
Lean arithmetic controls; they are not new public Lean network theorems.

The remaining substantive tasks are the marked-span presentation for the
lower bound, a global graph-mixing identity for the construction, and the
two complete real-parameter three-core formulas for five inputs. The latter
would yield either a matching (16,5) construction or the matching fixed-layer
minimum 6 if both sign classes were independently excluded.
