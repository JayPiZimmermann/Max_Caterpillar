# Overnight proof-search checkpoint, 25 October 2026, 02:49 UTC

The overnight search remains active. The two uniform targets are still open:
an unrestricted canonical all-tree exponential lower bound and an exact
two-hidden-layer construction of size 2^{O(N)}. The paper's construction
bound remains 2^{O(N log N)}.

## Matched five-input results

The minimum possible first hidden layer width is now proved to be **nine**,
with arbitrary real weights and biases, no skip connections, and any finite
second hidden layer. The independently verified (9,14) rational network
attains that first width. Fourteen is not claimed optimal.

The lower bound combines the complete exact real-coefficient classification
of possible first hidden layers of width eight with a short curvature
obstruction excluding every finite second hidden layer over its sole
surviving feature map. The continuous curvature-score identities are Lean
checked; the geometric argument and finite classification are separately
proved and independently checked, not a Lean network theorem.

Sources: `best5/overnight_fixed_natural8_rectangle.md`,
`best5/overnight_fixed_first9_paper.tex`, and their manifests. Root replays
passed the five-row classification, all 58,176 six-row sign profiles, the
Lean score lemma, and the exact global 120-cone network check.

For the prescribed ten-row first hidden layer, the minimum second hidden
layer width remains exactly six. Both matched results are in the paper.
Unmatched small-arity vocabulary examples were removed. The full first-nine
second-width optimum and the unrestricted second-width optimum remain open.

The only remaining row-sum count splits at first width nine are (1,1,7) and
(2,2,5), in the order (positive,negative,zero). This is not a classification
of the seven zero-sum features. The live fixed-nine P4 search is testing
arbitrary four-free-unit representations; its current upper remains (9,14).

## Strongest new uniform counting results

All statements below retain the model restrictions in their source notes.
They are mathematical arguments, not newly added public Lean theorems.

* Arbitrary real heads, signed inner/output weights, biases, and arbitrary
  comparison graphs of fixed degree Delta>=3 require
  Omega_Delta((1+y_Delta)^N), where
  y_Delta=(Delta-2)^(Delta-2)/(Delta-1)^(Delta-1). Subcubic graphs give
  Omega((5/4)^N). Degree-two graphs have the stronger separate bound
  Omega(2^N/N^(7/2)). Cycles are allowed.
* Add those weighted graphs to both original caterpillar/specified-rooted-
  star face dictionaries: degree at most three gives
  Omega((7/6)^N/sqrt(N)); fixed Delta>=4 gives the same pure exponential
  degree-dependent bound. All canonical stars, or all canonical trees of
  matching number at most two, can be adjoined for free without changing
  these asymptotic rates. Count only terms outside the free class.
* For weighted pseudoforests with nu+z>=k (matching size plus number of
  isolated vertices), the pure bound is of order (4/3)^k/(1+k^2).
* Mixtures of both original dictionaries with weighted pseudoforests of
  matching size at least k now satisfy
  Z >= (16/13)^k/[20(1+3k/13+9 binom(k,2)/169)] for N>=12, 2k<=N.
  All canonical stars can be free once N>=20; canonical matching-number-
  two trees can be free once N>=28.
* Graph excess b(G)=sum_C max(0,|E(C)|-|V(C)|) may be sublinear. If
  k=Omega(N), b=o(N), pure graph families retain rate
  exp(k log(4/3)-o(N)); mixtures retain exp(k log(16/13)-o(N)).

The clean proofs are `trees/overnight_upper_connected_coefficients.md`,
`trees/overnight_matching_mixture_mode.md`,
`trees/overnight_matching_mixture_coefficients.md`, and
`trees/overnight_free_class_asymptotics.md`. Do not mistake the free
canonical stars for arbitrary weighted or arbitrary real-head stars.

For all canonical trees with every root, orientation, and face state, the
proved unrestricted bound remains binom(N,4)/35 for N>=7. The nine-label
extension is still checking: 1,584 of 1,971 selected rational rows passed
both independent exact arithmetic engines at this checkpoint. It is not
yet a theorem. Even completion would give a stronger polynomial bound,
not the missing exponential result.

## Current uniform proof routes and exact obstructions

The lower-bound target is an actual top-quotient functional separating the
maximum from all trees without a perfect matching at every sufficiently
large odd arity. This would give the independently proved conditional
Fibonacci count Omega((2/phi)^N). The finite exceptions do not matter.
Several candidate tree scores satisfy local identities but fail actual
whole-function identities; Q2 remains only a candidate. Scalar rectangle
curvature assemblies also fail to descend through lower-dimensional facet
maxima. Complete opposite-face flags remain the live filtration-respecting
route.

The construction search has a new coherent ordered homological recurrence
that avoids averaging over every facet injection. Its cubical filling
support still grows too quickly; no exponential complexity claim follows.
Explicit product homotopies for triangle cycles may give smaller relative
states. The full marked-ear extension of the specified six-label family
has been excluded exactly (ranks 780/781); the root replay passed all 348
rational identities and the complete source/attachment/minor checks.

A separate actual cyclic-graph family of size O(N^3 2^N), with two symmetric
vertex classes and fixed coefficients {-1,0,1}, fails already at five
labels. An independent 119-point integer-value separator checks every one
of its 556 raw symmetric representatives. This rejects only that explicit
family, not general cyclic constructions.

## Repository and paper

The paper builds to 46 pages with no overfull boxes or undefined references.
The matched first-width-nine result is in commit `bf27e90`; supporting
proofs are in `543625e` and `ecf07e7`. The stronger matching bounds are in
`397f678` and paper update `0d5545e`. Exact search controls and fresh replays
were checkpointed in `39bcb15`. These commits were pushed to `main`.

The historical public Lean certificate still checks 122 statements from
24 October; it does not certify the subsequent prose arguments or new
network-classification theorem. The paper states that boundary explicitly.
