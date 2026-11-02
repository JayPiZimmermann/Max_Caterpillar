# Closed affine-skip lower bound in original feeding width

The strengthened [FeedingSharp theorem](../../../MaxCaterpillar/Frontier/RandomRestriction/FeedingSharp.lean)
improves the constant below by a factor of ten, to `1/40000000`, with the same
scope and threshold. See [its proof and audit](feeding_sharp_notes.md).

The strongest new theorem is `FeedingCore.affine_feeding_tradeoff` in
`FeedingTransfer.lean`. For `N ≥ 1040`, every exact real network of the form

```
f(x) = Σₖ dₖ σ(Σⱼ Wₖⱼ σ(Aⱼ·x+bⱼ) + Uₖ·x + θₖ)
       + Σⱼ Bⱼ σ(Aⱼ·x+bⱼ) + L·x + β
```

satisfies

`h₂ ≥ min(N², N⁴/h₁′) / 400000000`,

where `h₁′ = |{j : ∃ k, Wₖⱼ ≠ 0}|` is the original feeding count before any
normalization, deletion or freezing. All parameters and biases are arbitrary
real numbers, and exactness concerns every real input. No bound on total first
width or feeding width is assumed. The direct corollary
`affine_feeding_quadratic` gives `h₂ ≥ N²/400000000` when `h₁′ ≤ N²`, even with
arbitrarily many additional output-only first neurons.

This matches the affine-skip/feeding-width scope of Jensen's Theorem 1 and
removes its logarithmic loss. It proves a quadratic result; it does not prove
an exponential bound or an exponent greater than two.

The proof separates five exact operations:

1. The independently checked affine normalization preserves the original
   first and second index types and proves feeding lineage. Its normalized
   feeding count is therefore at most the original `h₁′`.
2. A feeding-masked core preserves every original second inner function and
   every ambient aggregate interaction graph. It is used for counting and
   is not incorrectly claimed to preserve the full output function.
3. For the actual five-input obstruction, arbitrary first-output terms are
   instead absorbed into tagged auxiliary outer slots. This construction
   preserves the full evaluation and normalization. Auxiliary slots have
   identically empty interaction graphs, so the matching witness must select
   an original second neuron. Their number never enters the final count.
4. Half restriction averages only over the feeding subtype. One actual
   half-model with the same original widths simultaneously satisfies the
   fourth-moment, nonbraid-count and regularized-moment budgets charged to
   that feeding count. Positive feeding width is proved using the actual
   five-input obstruction, rather than assumed.
5. The same cost-400 per-neuron estimate and scalar optimizer apply. The
   large-feeding-width regime uses the independently proved skip-safe
   inequality `N ≤ 2h₂+2`, preserving the constant `1/400000000`.

The independent driver `verification/h2/AffineFeedingTradeoffCheck.lean`
expands all nine primitive parameter arrays/scalars and the denominator as
the cardinality of the original nonzero-column subtype. It also checks the
simultaneous half-model contract, audits ten transitive axiom sets, and
applies the stronger quadratic feeding theorem to a genuine caterpillar
network at the boundary arity `N=1040`, proving its feeding-width hypothesis.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.

Reproduce the source-bound gate with
`python3 research/sN/jensen_bound/affine_feeding_recheck.py --run`.
