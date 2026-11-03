# Round 2 claim scope audit

Read-only review of the four requested frozen developments. This review did
not run Lean or change a producer file. The publication inventory owner
checks source/log hashes separately. No public GitHub commit is presumed for
the new files below; the paths and line numbers identify local source only.

## Actual cycle/forest network bridge

Namespace: `MaxCaterpillar.ExponentialPush.CycleBridge`.

* `matchingRepresentable_iff_coverRepresentable` —
  `cycle_bridge/Equivalence.lean:37`.
* `localMatchingObstruction_iff_no_cover_representation` —
  `cycle_bridge/Equivalence.lean:70`.
* `exists_expansion` — `cycle_bridge/NetworkExpansion.lean:93`.
* `expanded_width_le` — `cycle_bridge/NetworkExpansion.lean:80`.
* `expanded_graph_acyclic` — `cycle_bridge/ExpandedGraphs.lean:27`.
* `expanded_graph_le_original` — `cycle_bridge/ExpandedGraphs.lean:39`.
* `expanded_small_covers` — `cycle_bridge/ExpandedGraphs.lean:52`.

For every input arity N, nonnegative integer r and real function f, finite
translation-normalized homogeneous braid-network representability with
matching number at most r in every second-hidden interaction graph is
equivalent to representability with vertex cover at most r in each graph.
The graph is the actual signed aggregate over parallel first rows; the
construction does not replace it with the union of raw row supports.

The exact MAX consequence is H(N,r+1) iff there is no such cover-r MAX_N
network, with N nonzero for the existing maximum definition. The finite
network indices, normalization, output remainder and equality on every real
input are derived by the implementation. The new width is bounded by the
old second hidden width times 3 to the number of unordered input pairs.

This is not a width-preserving transformation, a new exclusion at r=2, or
an unrestricted affine/bias theorem stated directly on the nine-array
model. It is a theorem about the normalized homogeneous braid model used by
the structural obstruction. The README makes these limits explicit and
correctly calls these representability classes rather than vector spaces:
normalization fixes the diagonal translation slope at one.

The core rechecker rebuilds all research dependencies in import order and
the production imports, then checks independent expanded contracts and
genuine triangle/empty-cover controls. No missing model bridge was found
in this reviewed theorem chain. The recorded receipt has 15 standard-only
axiom reports and 198 source/control hashes.

## H(5,2) using cycle deletion and only the star certificate

Namespace: `MaxCaterpillar.ExponentialPush.CycleBridge`.

* `no_cover_one_maximum_five` — `cycle_bridge/FiveViaCover.lean:37`.
* `localMatchingObstruction_five_two_via_cycle_deletion` —
  `cycle_bridge/FiveViaCover.lean:67`.

The latter is literally `LocalMatchingObstruction 5 2`: an original
second-hidden neuron of every exact translation-normalized braid MAX_5
network has a two-edge disjoint matching. It uses the completed same-arity
matching/cover bridge and the existing all-real star certificate. The proof
retains arbitrary real heads, signed coefficients, output skips and actual
parallel cancellations within that model.

This is a second proof of an existing result, not a stronger width bound.
The README accurately states that the new proof removes the specialized
triangle modules but increases the complete project module count and byte
count. It does not advertise a smaller overall Lean proof closure or a
certificate-free proof. Its recheck requires the separately rebuilt core
cycle bridge; this dependency is stated explicitly. Six axiom reports and
the independent counter-input/matching/empty and nonempty cover controls
are recorded by its receipt.

## Support transversals: a genuine first-width relaxation

Namespace: `MaxCaterpillar.Overnight.SupportTransversal`.

* `BraidOnRetained` — `portfolio/transversal/Model.lean:15`.
* `exists_braid_model` — `portfolio/transversal/Model.lean:22`.
* `normalized_braid_quadratic` — `portfolio/transversal/Bounds.lean:17`.
* `affine_retained_quadratic` — `portfolio/transversal/Bounds.lean:49`.
* `conditional_affine_retained_lower_bound` —
  `portfolio/transversal/Bounds.lean:59`.
* `affine_transversal_quadratic` — `portfolio/transversal/Bounds.lean:73`.

For an actual arbitrary-real nine-array affine-skip network computing MAX_N,
let C meet the support of every original first row whose bias and coordinate
sum are both zero and whose support has size at least three. If
m = N - |C| is at least three, the theorem gives

    original h2 >= m² / 3,000,000.

There is no bound on total first hidden width. The exact localization
constructs a model on the retained input embedding with both original
hidden widths unchanged. Rows not contained in the retained set become
affine at the proved generic top tie. The original bias-zero condition is
sound because the faithful normalization retains precisely the zero-bias,
zero-sum first rows; it is not a dropped assumption about arbitrary biased
rows. Output-only rows are included in the transversal premise.

The separate growing-matching consequence gives (23/25)4^q when q >= 1,
160000 q² <= m, and H(4q+1,q) is explicitly assumed. This remains conditional
at growing q. A small transversal is a structural hypothesis, not something
guaranteed for every large collection of supports.

The README matches these source types. The receipt records nine axiom
reports, literal nine-array and transversal contracts, and a genuine exact
MAX3 control. No hidden first-width cap or feeding-only claim was found.

## Coordinate quotient: exact transport, not a stronger deletion criterion

Namespace: `MaxCaterpillar.Overnight.CoordinateQuotient`.

* `eval_quotient` — `portfolio/coordinate_quotient/Model.lean:63`.
* `quotient_computes_max` — `portfolio/coordinate_quotient/Model.lean:84`.
* `BraidBlockSums` — `portfolio/coordinate_quotient/Model.lean:94`.
* `exists_normalized_braid_quotient` —
  `portfolio/coordinate_quotient/Model.lean:115`.
* `exists_braid_retained_of_quotient` —
  `portfolio/coordinate_quotient/Section.lean:47`.
* `affine_quotient_quadratic` —
  `portfolio/coordinate_quotient/Bounds.lean:13`.
* `conditional_affine_quotient_lower_bound` —
  `portfolio/coordinate_quotient/Bounds.lean:23`.

An arbitrary coordinate map transports evaluation exactly by block-summing
all input covectors and preserving hidden indices, weights, biases and skips.
A surjective map from N coordinates to m coordinates transports MAX_N to
MAX_m. If every original zero-bias, zero-sum first row has block-sum support
at most two, this gives h2 >= m²/3,000,000 for m >= 3, without an h1 cap.
The exponential-form corollary has the same explicit H premise as the
transversal result.

The section theorem constructs an m-coordinate retained embedding satisfying
the transversal model's predicate. Thus this criterion cannot improve the
optimal retained-coordinate size. The README states this limitation plainly;
counting coordinate quotient as a separate stronger unrestricted bound would
be misleading. Surjectivity is checked by a noninjective positive control
and a nonsurjective countercontrol. The recorded receipt has 13 axiom reports
and says its complete rebuild ran.

## Verdict

No theorem/README scope mismatch or missing mathematical bridge was found in
these four reviewed developments. The support-transversal bound is a new
structural way to drop the first-width cap. The cycle equivalence is a new
general reduction. The five-input proof is an alternative proof, and the
coordinate quotient is an exact model transformation whose comparison with
deletion is itself verified. None of the four proves the currently open
growing structural obstruction or an unconditional unrestricted exponential
second-hidden-width lower bound.

## Follow-up: sharper feeding and support-budget conditional bounds

This follow-up reviews the source types and their explanatory scope. The
publication owner must separately confirm that the final aggregate gates
have finished and that their frozen hashes match. It does not treat a
pending gate as a passed receipt.

Namespace: `MaxCaterpillar.ExponentialPush.WidthTradeoff`.

* `conditional_affine_feeding_sharp` — `h1_tradeoffs/SharpTradeoff.lean:15`.
* `sharpParameter` — `h1_tradeoffs/SharpTradeoff.lean:46`.
* `conditional_affine_feeding_sharp_explicit` —
  `h1_tradeoffs/SharpTradeoff.lean:62`.
* `conditional_affine_feeding_sqrt_coefficient` —
  `h1_tradeoffs/SharpTradeoff.lean:97`.
* `originalSupportBudget` — `h1_tradeoffs/WeightedTradeoff.lean:37`.
* `conditional_affine_support_tradeoff` —
  `h1_tradeoffs/WeightedTradeoff.lean:68`.

The explicit feeding theorem counts
F = the number of ORIGINAL W-columns having at least one nonzero entry.
With n = floor(N/2), its actual integer parameter is

    d = 1 + Nat.sqrt(floor(105 F / (16 n²))).

The size premise is n >= 10¹⁰ d². The local obstruction premise is
H(4q+1,q), where q = floor(sqrt(n)/(8000d)). The conclusion on the original
second-hidden width is

    h2 >= exp(3 sqrt(n)/(8000d))/2.

All nine primitive real arrays are unrestricted apart from exact MAX and
the displayed premises; there is no total first-width cap. Output-only
first neurons are uncharged. This is a conditional tradeoff: increasing F
or choosing a different parameter changes q and hence changes the H premise.
It does not establish H at these growing orders, and a joint large-arity
H/network witness is not claimed.

The coefficient corollary allows F <= C N² with
s = Nat.sqrt(C-1)+1. For integer C >= 1, s is exactly ceil(sqrt(C)); for
C=0 the definition returns 1. The theorem uses d=6s, the corresponding
size and H premises, and gives

    h2 >= exp(3 sqrt(n)/(48000s))/2.

The weighted theorem replaces even the count F with an original-row sum.
Only rows with zero original bias, zero coordinate sum, a nonzero original
W-column, and support size r <= n contribute. Their weight is w(r)/2^r,
where w(r)=0 for r<=2, w(3)=1, and w(r)=(r)_4 for r>=4. A budget at most
d²n² gives the same conditional conclusion. It counts multiplicities;
the distinct-support profile results are separate declarations. Clipping
supports larger than n is part of the proved half-restriction model, not
an assumption that a nonlinear row can be partially truncated.

The README matches these types. Its asymptotic interpretation
min(sqrt(N), N^(3/2)/sqrt(F)) must retain the size premise and H. It correctly
distinguishes F=o(N³) for a diverging exponent from the stronger
F=o(N³/log²N) for a superpolynomial conclusion. These are prose mathematical
consequences, not separate Lean asymptotic declarations. The minor redundant
closing parenthesis in the displayed README definition of d is typographical;
the Lean definition and expanded rounding checks are unambiguous.

## Follow-up: actual degree-two exponential theorem

Namespace: `MaxCaterpillar.Overnight.DegreeTwo`.

The strongest raw theorem is in **`SharpBound.lean`**, not a file called
`RawSharpBound.lean`:

* `raw_width_binomial_sharp` — `degree_two/SharpBound.lean:34`.
* `raw_width_exponential_sharp` — `degree_two/SharpBound.lean:53`.
* `raw_width_exponential_sharp_real` — `degree_two/SharpBound.lean:65`.
* `normalized_width_binomial_sharp_feeding` —
  `degree_two/SharpBound.lean:17`.

The older `RawBound.lean:20`, `:41`, and `:54` declarations retain the
coarser compatibility bounds. The sharp binomial theorem says, for every
m>=3,

    2 choose(N,m) <= h2 [2N + (m-1)N²].

For N>=6, its real corollary gives

    h2 >= 4 * 2^N / [N³(N+1)].

The raw source requires every ORIGINAL first covector to have coordinate
sum zero and support at most two, equivalently a scalar coordinate
difference or zero. Each original second-neuron interaction graph must have
degree at most two at every input vertex. These are per-neuron graphs; their
union need not have degree at most two. There is no h1 cap. Arbitrary biases,
heads, output skips and coefficient signs remain allowed.

The raw interaction graph is literally nonvanishing signed
`braidEdgeWeight net.A (net.W k) a b` at distinct vertices; it is independent
of the first-row biases and includes parallel cancellations. The recession
model preserves every first covector and first-to-second weight. Subsequent
normalization zeros or retains a whole second row, so it cannot unmask
cancelled original edges by deleting individual first rows. This resolves
the main model risk in the arbitrary-bias statement.

The normalized sharp theorem weakens the braid-support requirement to
feeding first rows, but still assumes translation normalization for every
first row. The displayed RAW theorem does not yet inherit that weaker
first-row condition. Do not describe the raw theorem as allowing arbitrary
output-only first covectors.

No matching obstruction is a hypothesis: this implication is unconditional
within the stated architecture class. Its established concrete nonvacuity
control is MAX4 at widths (2,1). The development does not establish an exact
degree-two MAX_N construction for N>=6. Consequently it does not prove
exponential sufficiency, optimality, or even nonemptiness at those arities.
The README prominently states this limitation and attributes the earlier
degree-two mathematical route to the repository's 25 October note.

## Follow-up: the unconditional 175000 quadratic constant

Namespace: `MaxCaterpillar.OvernightConstants.Theta`.

* `model_bound` — `constants/ThetaQuadratic.lean:21`.
* `normalized_quadratic` — `constants/ThetaQuadratic.lean:80`.
* `affine_quadratic` — `constants/ThetaQuadratic.lean:125`.

The strongest requested raw contract is:

    N >= 3, exact MAX_N on every real input, total original h1 <= N²
    imply original h2 >= N²/175000.

The affine-skip model permits arbitrary real weights, all biases, all input
and first-hidden output skips, and unrestricted first covectors. There is
no H premise, graph-degree restriction, support budget, probability estimate,
or normalization condition left in this raw signature. The actual proved
H(5,2) theorem is imported inside the proof.

`ThetaCheck.lean:13` supplies
`MaxCaterpillar.OvernightConstants.Theta.Check.raw_nine_array_contract`.
Its other contracts expose the simultaneous actual half-model budgets and
the actual uniform-permutation isolated-gap event, so the constant is not
merely an assumed stronger tail rate. The driver includes actual caterpillar
nonvacuity witnesses at N=3 and N=50001, the first odd dimension beyond the
small-arity branch, retaining their large second widths symbolically.

The prose in `ThetaCheck.md` matches the source: the model constant is
42200, the raw rounding ratio is at most 4.1, and 4.1*42200=173020<175000.
This scope review found no hidden structural assumption or obvious
normalization mismatch. Publication should wait for the final source-bound
Theta gate; the presence of the source and audit prose alone is not that
gate.
