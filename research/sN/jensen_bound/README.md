# Second-hidden-layer lower bounds for exact MAX networks

For total first hidden width `h₁ ≤ N²`, the improved verified bound is

\[
h_2 \ge \frac{N^2}{10000000},\qquad N\ge3.
\]

It allows arbitrary real weights, biases, and every affine skip connection.
It uses the proved five-input obstruction, with no structural conjecture.
This is forty times the constant of our original quadratic theorem.

- [Improved quadratic theorem](../../../MaxCaterpillar/Frontier/RandomRestriction/QuadraticCutoff.lean#L123)
- [Independent expanded network contract](../../../verification/h2/QuadraticCutoffCheck.lean)
- [Source-bound receipt](quadratic_cutoff_receipt.json) and [proof explanation](quadratic_cutoff_notes.md)

The more general feeding-width tradeoff also permits arbitrary real weights,
biases, and every affine skip connection. Let `h₁′` be the number of ORIGINAL
first-hidden neurons with some nonzero weight into the second hidden layer.
For `N ≥ 1040`, exact equality with `MAX_N` on every real input implies

\[
h_2 \ge \frac{1}{40000000}\min\left(N^2,\frac{N^4}{h_1'}\right).
\]

In particular, `h₁′ ≤ N²` implies `h₂ ≥ N²/40000000`, even with arbitrarily
many additional output-only first neurons. No first-width cap, normalization,
support budget, probabilistic estimate or certificate is assumed in the
public theorem. For any fixed positive `C`, the condition `h₁′ ≤ C N²` gives
quadratic growth with constant `1/(40000000 max(1,C))`.

- [Full affine-skip theorem and quadratic corollary](../../../MaxCaterpillar/Frontier/RandomRestriction/FeedingSharp.lean#L46)
- [Independent nine-array and ORIGINAL feeding-count contract](../../../verification/h2/AffineFeedingSharpCheck.lean)
- [Full-scope source-bound receipt](feeding_sharp_receipt.json)
- [Detailed proof and exact scope](feeding_sharp_notes.md)
- [Earlier ordinary-network theorem](../../../MaxCaterpillar/Frontier/RandomRestriction/NetworkLowerBound.lean#L17)
- [Constructive skip encoder and simple scope extensions](width_extensions_notes.md)

The finite constants remain conservative. Even the improved total-width
quadratic expression exceeds `N/2` only when `N > 5000000`.

## Proof route

1. Normalize the actual affine-skip network while preserving both original
   neuron index types and proving that no new first neuron starts feeding.
2. Restrict to half the input coordinates. One restriction simultaneously
   controls the fourth support moment and the count of non-braid feeding rows.
3. Select five remaining inputs and a structured point on the others. The
   closed finite coefficient certificate forces an original surviving second
   neuron whose interaction graph contains two disjoint selected edges.
   Output-only first terms are absorbed into auxiliary slots with empty
   interaction graphs, so these slots cannot supply that witness.
4. Exclude three explicitly bounded bad events. On the remaining permutation
   fibers, actual adjacent swaps produce independent coin directions. Exact
   summed edge coefficients retain all parallel-row cancellations.
5. A bounded size-bias coupling gives per-neuron probability at most `400/K²`.
   Sum over original second neurons and optimize the cutoff. The independent
   skip-safe linear bound handles the large-first-width regime.

The improved total-width corollary uses the general finite transfer below at
the proved `H(5,2)`, with the larger cutoff `K = floor(m/25)`. It preserves the
matching factorial and cancels it against one exponential-series term. The
same argument therefore covers the unconditional quadratic theorem and the
conditional growing-order extensions.

The proof is computer-assisted: its finite coefficient certificate is checked
by Lean's kernel. Audited dependencies use only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorry`, project axioms, or `native_decide`.

## Optimality and further work

Quadratic growth is a proved lower bound, not a known optimal rate. The
repository's all-arity construction uses quadratic first width and
`2^{O(N log N)}` second width. Its dictionary-restricted exponential lower
bounds do not establish exponential width for arbitrary real networks.
The inspected [Tallavarjula–Rastegar construction](https://zenodo.org/records/23377648)
also has a factorial-size exact second layer. The quadratic-width result of
[Lu](https://shunqilu.github.io/publications/sharp-closure-thresholds.html)
concerns approximation closure with escaping parameters; it does not give an
exact finite-parameter network. These checks do not establish a globally best
upper bound or settle tightness.

The [growing-arity investigation](counting_routes/transfer/TRANSFER.md)
separates a conditional transfer from its unproved structural hypothesis.
The five-input obstruction alone does not establish that hypothesis at
larger arities. No unconditional exponential network bound is claimed.

The stronger conditional consequences have also passed Lean checks. The
new Bernoulli argument applies to arbitrary original first covectors, with
all biases and affine skips. For integer `C ≥ 1`, assume `h₁ ≤ C N²`, put
`n = floor(N/2)` and `q = floor(sqrt(n)/(160000 C))`, and suppose
`n ≥ 10¹⁰ (20C)²`. Under the explicit local obstruction `H(4q+1,q)`, it gives

\[
h_2 \ge \frac12\exp\!\left(\frac{3\sqrt n}{160000C}\right).
\]

See the [raw affine-network theorem](../../../MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/Bernoulli/AffineLowerBound.lean#L50),
[expanded nine-array contract](../../../verification/h2/AffineBernoulliLowerBoundCheck.lean),
[receipt](affine_bernoulli_receipt.json), and
[proof explanation](counting_routes/transfer/BERNOULLI.md).
The proof conditions a Bernoulli selected set on avoiding all internal
non-braid supports. Positive association preserves the required upper bounds
on selected-label probabilities, while a separate size estimate retains
enough selected coordinates. This improves the conditional general-row rate
from `exp(c N^(1/3) log N)` to `exp(c_C sqrt(N))`.

Two earlier finite consequences remain available:

- For a braid first layer, `q ≥ 1` and `160000 q² ≤ N` give
  `h₂ ≥ (23/25) 4^q`, assuming the explicitly defined local obstruction
  `H(4q+1,q)`. The [raw affine-network theorem](../../../MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/AffineBraid.lean#L38)
  permits biases and affine skips; the [square-root specialization](../../../MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/BraidSqrtCorollary.lean)
  makes the conditional `exp(c sqrt(N))` rate explicit.
- For a normalized arbitrary-row model with non-braid count and fourth
  support moment at most `d² n²`, the [general-row theorem](../../../MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/GeneralRows.lean#L79)
  gives `h₂ ≥ (1/2)(n/(400000 d q²))^q`, assuming `d,q ≥ 1`,
  `8000 d² ≤ n`, `1000 d² q³ ≤ n`, and the same `H(4q+1,q)`.

Here `H(k,q)` asserts that every actual normalized braid network computing
`MAX_k` has a second neuron whose summed interaction graph contains a
matching of size `q`. This is a structural assertion about all real weights,
not a numerical counting assumption. The growing levels remain open.
The displayed square-root rate is stretched exponential; it does not assert
a lower bound of the form `exp(c N)`.

## Provenance and verification

The obstruction and restriction/counting approach builds on Simon Moritz
Jensen's draft discussed in this project. The full-scope theorem removes the
logarithmic loss for quadratic feeding width and also removes the first-width
cap. The general bounded size-bias exponential-moment principle is from
[Arratia and Baxendale, Proposition 4.1](https://arxiv.org/abs/1306.0157).
Private drafts and correspondence are not included.

Reproduce the full theorem-specific build, expanded contract, source scan and
axiom audit with:

```sh
python3 research/sN/jensen_bound/feeding_sharp_recheck.py --run
python3 research/sN/jensen_bound/quadratic_cutoff_recheck.py --run
python3 research/sN/jensen_bound/affine_bernoulli_recheck.py --run
```

The [public-root gate](../zulip_three/public_claim_manifest.json) checks the
public width and Max4 claims through `import MaxCaterpillar`, and rebuilds
`All`:

```sh
scripts/lean_lock.sh python3 research/sN/zulip_three/check_public_claims.py
```
