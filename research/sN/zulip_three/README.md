# Verified width and Max4 fiber results

The [second-hidden-layer width theorem](../jensen_bound/README.md) proves
`h₂ ≥ min(N²,N⁴/h₁′)/40000000` for `N ≥ 1040`, including arbitrary real
weights, biases and affine skips. Here `h₁′` counts only original first neurons
feeding the second layer. Thus quadratic feeding width forces quadratic
second width. For total first width `h₁ ≤ N²`, a further verified corollary
improves the bound to `h₂ ≥ N²/10000000` for every `N ≥ 3`, with the same
affine-skip scope. A further [Bernoulli theorem](../jensen_bound/counting_routes/transfer/BERNOULLI.md)
proves a square-root exponential rate conditional on an explicitly stated
growing local obstruction; that structural hypothesis remains unproved.

The following Max4 theorems use ordinary real two-hidden-layer ReLU networks and equality
on every real input. The exact component count includes arbitrary biases and
the quotient by positive hidden-neuron rescalings, hidden permutations, and
input permutations.

| Result | Lean statement |
| --- | --- |
| Exactly 65 components at widths `(6,5)` | [GlobalComponents.lean](../../../MaxCaterpillar/Fiber/Count65/GlobalComponents.lean#L82) |
| Same natural activations along an exact path, different neuron-interchange outputs | [NaturalInterventions.lean](../../../MaxCaterpillar/Fiber/NaturalInterventions.lean#L210) |
| Identical complete gates, incomparable representations, regular exact-fiber endpoints | [RegularCounterexample.lean](../../../MaxCaterpillar/Fiber/GatingAbstractions/RegularCounterexample.lean#L16) |
| Strict binary gate changes within one exact component | [BinaryPatterns.lean](../../../MaxCaterpillar/Fiber/BinaryPatterns.lean#L200) |
| Equal global binary maps and matching nonzero readout signs imply an exact path | [GlobalConvexity.lean](../../../MaxCaterpillar/Fiber/BinaryPatterns/GlobalConvexity.lean#L81) |

The intervention example distinguishes suffix responses only at hidden vectors
that no real input attains. It does not show different natural activation maps
or establish algorithmic inequivalence. The representation-partition and binary
gate examples do distinguish ordinary-input hidden representations.

The regular all-input exact-fiber theorem allows all 45 weights to vary with
biases fixed to zero. A separate [empirical version allowing arbitrary
biases](../../../MaxCaterpillar/Fiber/GatingAbstractions/EmpiricalRegularity.lean#L278)
uses its specified four-input dataset.

The 65-component proof is the exhaustive actual-network decomposition into
one paired component, 32 mixed components, and 32 star components. See the
[proof explanation](count65_proof.md).

Verification:

- [Public claim manifest](public_claim_manifest.json)
- [Handwritten exact-type checks](../../../verification/fiber/ZulipThreePublicCheck.lean)
- [Public-root and `All` verification receipt](public_claim_receipt.json)
- [Exact-count semantic and axiom audit](count65_receipt.json)

All audited theorem dependencies use only `propext`, `Classical.choice`, and
`Quot.sound`. The included receipts bind the verified source contents by
SHA-256. The public gate can be rerun with:

```sh
scripts/lean_lock.sh python3 research/sN/zulip_three/check_public_claims.py
```
