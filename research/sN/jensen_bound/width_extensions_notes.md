# Scope extensions of the closed ordinary-network bound

Jensen's Theorem 1 (PDF, page 2) permits affine skip connections and charges
`h₁′`, the number of first neurons with a nonzero weight into the second
hidden layer. Those are two distinct changes to the previously closed
ordinary-network theorem. The canonical `MaxCaterpillar.Frontier.RandomRestriction` leaves prove the
following constructive extensions.

## Ordinary networks: charge only feeding first neurons

`FeedingWidthExtension.lean` defines the exact finite count
`feedingCount = |{j : Fin h₁ : ∃ k : Fin h₂, W₂[k,j] ≠ 0}|`.
It constructs a literal ordinary network of widths `(feedingCount, h₂)` by
removing all other first neurons. The theorem `prune_eval` proves equality
on **every** real input, with all original biases retained. This yields

`h₂ ≥ min(N², N⁴/feedingCount) / 400000000` for `N ≥ 1040`.

In particular `feedingCount ≤ N²` implies the explicit quadratic bound,
regardless of how many unused first neurons the original network contains.

## Fully affine skips: a bound in total first width

`AffineSkipExtension.lean` uses nine unrestricted parameter arrays/scalars and
the literal formula

```
f(x) = Σₖ dₖ σ(Σⱼ Wₖⱼ σ(Aⱼ·x+bⱼ) + Uₖ·x + θₖ)
       + Σⱼ Bⱼ σ(Aⱼ·x+bⱼ) + L·x + β.
```

The exact encoder adds first neurons `σ(xᵢ)` and `σ(−xᵢ)` for each coordinate.
These transmit all affine input skips. Two extra second neurons carry
`σ(F(x))−σ(−F(x))=F(x)`, where `F` is the entire output skip. The resulting
ordinary network has widths `(h₁+2N,h₂+2)` and computes exactly the same
function on every real input, including all biases. Therefore

`h₂+2 ≥ min(N², N⁴/(h₁+2N)) / 400000000`.

The separately proved ordinary first- and second-width bounds applied to
this exact encoding imply `h₁ ≥ 2N` and `h₂ ≥ 2` when `N ≥ 1040`.
Absorbing both shifts gives the cleaner unconditional result

`h₂ ≥ min(N², N⁴/h₁) / 1600000000`.

This proves `Ω(N²)` at total first width `O(N²)` in the complete affine-skip
model. The stronger full-skip feeding-width theorem is now proved separately
in [FeedingTransfer](../../../MaxCaterpillar/Frontier/RandomRestriction/FeedingTransfer.lean).
The further [FeedingSharp refinement](../../../MaxCaterpillar/Frontier/RandomRestriction/FeedingSharp.lean)
improves the full-scope constant to `1/40000000`. The simple pruning/encoding
argument here remains useful, but pruning alone cannot discard output-only
first terms in the skip model.

## Completed route to feeding width with affine skips

The following repair is now verified; see [full-scope notes](affine_feeding_notes.md)
and [its receipt](affine_feeding_receipt.json).

1. For the probability/count model, zero every nonfeeding first covector and
   set `B=0`. All original second inner functions and their interaction graphs
   remain exactly unchanged, since the corresponding `W` columns vanish.
   The per-neuron bound requires no MAX identity and can count this masked
   model. Its bad events now charge only feeding supports.
2. Inside the local structural contradiction, retain the entire target
   identity by moving each output-only term `Bⱼ σ(Aⱼ·x)` into a tagged auxiliary
   outer slot with `d=Bⱼ`, `U=Aⱼ`, and `W=0`. Translation normalization is
   preserved. Such auxiliary slots have empty interaction graphs. Consequently
   the two-disjoint-edge witness must belong to an original second neuron;
   the auxiliary count never enters the final event union.
3. Average the half-restriction support costs over the original feeding
   subtype and use the already proved feeding-lineage lemmas. Derive positive
   feeding count: zero feeding collapses the entire skip network to one hidden
   layer, and the existing free-neuron bound with no genuinely nested gates
   rules out `MAX_N` for `N≥3`.
4. An explicit arbitrary-affine-skip-to-homogeneous-normalized bridge
   preserves original indices and feeding lineage. The half restriction and
   scalar optimizer then complete the original-feeding-width theorem.

## Verification

`verification/h2/WidthExtensionsCheck.lean` independently checks the feeding
subtype count, literal encoding widths/evaluation, fully expanded nine-array
affine-skip formula, and a genuine ordinary caterpillar construction embedded
into the skip model at the exact boundary `N=1040`. The major extension
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

Reproduce the source-bound extension gate with
`python3 research/sN/jensen_bound/width_extensions_recheck.py --run`.
