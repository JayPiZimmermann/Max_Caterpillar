# Quadratic second-hidden-layer lower bound

For every ordinary two-hidden-layer ReLU network computing
`MAX_N` on every real input, with arbitrary real weights and biases, the
formalization proves, for `N ≥ 1040`,

\[
h_2 \ge \frac{1}{400000000}\min\left(N^2,\frac{N^4}{h_1}\right).
\]

In particular, `h₁ ≤ N²` implies `h₂ ≥ N² / 400000000`. More generally,
for any fixed positive `C`, `h₁ ≤ C N²` gives a quadratic lower bound with
constant `1 / (400000000 max(1,C))`. All first-hidden-layer neurons count
toward `h₁`. The public theorem has no normalization, parity, support,
probability, or certificate hypothesis. The network model has no skip
connections.

- [Tradeoff and quadratic corollary](../../../MaxCaterpillar/Frontier/RandomRestriction/NetworkLowerBound.lean)
- [Independent contract expanded into all six parameter arrays](../../../verification/h2/NetworkLowerBoundCheck.lean)
- [Source-bound verification receipt](network_lower_bound_receipt.json)
- [Proof structure and scope](network_lower_bound_notes.md)

The finite constant is conservative. The independent linear bound `N ≤ 2h₂`
is stronger over a substantial finite range; when `h₁ ≤ N²`, the displayed
quadratic expression exceeds `N/2` only for `N > 200000000`.

## Proof route

1. Restrict an actual network to half the input coordinates. A single
   restriction controls both the fourth support moment and the number of
   non-braid first-hidden rows, while retaining the original neuron indices.
2. Choose five remaining coordinates and a structured point on the others.
   An exact finite coefficient certificate forces an original surviving
   second-hidden neuron whose interaction graph contains two disjoint edges.
3. Exclude three explicitly counted bad events. On every remaining
   permutation fiber, actual adjacent swaps give independent coin directions
   in that neuron's preactivation equation. Higher-support rows are excluded
   from changing these directions; arbitrary parallel-row cancellations are
   included in the exact signed edge coefficients.
4. A bounded size-bias coupling bounds the resulting matching moment. The
   complete per-neuron event has probability at most `400/K²`.
5. Sum over the original second-hidden neurons and optimize the cutoff.
   The independent linear bound handles the large-first-width regime.

The proof uses a finite coefficient certificate, so it is computer-assisted.
All certificate leaves and the actual-network assembly are checked by Lean's
kernel. Audited dependencies use only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorry`, project axioms, or `native_decide` are used.

## Provenance and verification

The obstruction and restriction/counting approach builds on Simon Moritz
Jensen's draft discussed in this project. The present assembly sharpens the
quantitative step and removes the logarithmic loss for `h₁ = O(N²)`. The
general bounded size-bias exponential-moment principle is from
[Arratia and Baxendale, Proposition 4.1](https://arxiv.org/abs/1306.0157).
The draft itself and private correspondence are not included here.

Reproduce the theorem-specific build, expanded contract, source scan and
axiom audit with:

```sh
python3 research/sN/jensen_bound/network_lower_bound_recheck.py --run
```

The [public-root gate](../zulip_three/public_claim_manifest.json) additionally
checks that both width theorems and the seven Max4 fiber claims are available
through `import MaxCaterpillar`, and rebuilds `All`:

```sh
scripts/lean_lock.sh python3 research/sN/zulip_three/check_public_claims.py
```
