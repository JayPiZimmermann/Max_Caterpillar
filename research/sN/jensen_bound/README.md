# Second-hidden-layer lower bounds for exact MAX networks

The strongest verified theorem permits arbitrary real weights, arbitrary
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

The finite constant is conservative. For ordinary networks with `h₁′ ≤ N²`,
the displayed quadratic expression exceeds the independently known `N/2`
bound only when `N > 20000000`.

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

The proof is computer-assisted: its finite coefficient certificate is checked
by Lean's kernel. Audited dependencies use only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorry`, project axioms, or `native_decide`.

## Optimality and further work

Quadratic growth is a proved lower bound, not a known optimal rate. The
repository's all-arity construction uses quadratic first width and
`2^{O(N log N)}` second width. Its dictionary-restricted exponential lower
bounds do not establish exponential width for arbitrary real networks.

The [growing-arity investigation](counting_routes/transfer/TRANSFER.md)
separates a conditional transfer from its unproved structural hypothesis.
The five-input obstruction alone does not establish that hypothesis at
larger arities. No unconditional exponential network bound is claimed.

Two stronger conditional consequences have also passed Lean checks:

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
```

The [public-root gate](../zulip_three/public_claim_manifest.json) checks the
public width and Max4 claims through `import MaxCaterpillar`, and rebuilds
`All`:

```sh
scripts/lean_lock.sh python3 research/sN/zulip_three/check_public_claims.py
```
