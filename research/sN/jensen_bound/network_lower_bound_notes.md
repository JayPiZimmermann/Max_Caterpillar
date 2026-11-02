# Actual ordinary-network width tradeoff

The public declarations are in
`MaxCaterpillar/Frontier/RandomRestriction/NetworkLowerBound.lean`:

- `NetworkLowerBound.second_width_tradeoff`: for every ordinary two-hidden-layer
  real ReLU network computing `MAX_N` on **all** real inputs, if `N ≥ 1040`,
  then `h₂ ≥ min(N², N⁴/h₁) / 400000000`.
- `NetworkLowerBound.second_width_quadratic`: under the additional bound
  `h₁ ≤ N²`, the conclusion is `h₂ ≥ N² / 400000000`.

The network is the repository's six-array `Network N h₁ h₂`, with arbitrary
real weights and arbitrary biases in both hidden layers and the output. It has no skip connections.
The theorem derives input-arity positivity from `N ≥ 1040`; the caller supplies
no normalized model, certificate, support budget, probability estimate, or
generic scale. The constant is explicit and conservative. This proves a
quadratic lower bound at quadratic first width; it does not prove a power
strictly greater than two.

The proof uses one actual restriction to `n = floor(N/2)` inputs with the same
original first- and second-neuron index types. Its full-index support moment
`A = max(Σⱼ 1[|supp Aⱼ|≥3]|supp Aⱼ|⁴, 1)` and nonbraid count `M` satisfy
`4A ≤ 81h₁` and `4M ≤ h₁`. When `1000h₁ ≤ N³`, the actual restriction also
satisfies `240M ≤ n(n−1)(n−2)`. The opposite regime follows from the separately
proved ordinary-network inequality `N ≤ 2h₂`.

On the literal three-permutation experiment, the three excluded events have
fractions at most `1/4`, `2/25`, and `1/4`. The closed all-real five-variable
star certificate supplies a genuine original-neuron witness outside their
union. Each original neuron covers at most `400/K²` of the sample space.
Consequently `0.42K² ≤ 400h₂` for every admissible integer cutoff. The scalar
optimizer turns these inequalities into the displayed tradeoff.

`verification/h2/NetworkLowerBoundCheck.lean` checks the exact headline, a
contract with all six arbitrary parameter arrays and the fully expanded
two-ReLU-layer evaluation formula, the quadratic corollary, and a genuine
ordinary caterpillar-network witness at the boundary arity `N=1040`. It audits
the transitive axioms of the major bridges and both public declarations.

The reproducible gate is
`python3 research/sN/jensen_bound/network_lower_bound_recheck.py --run`.
Its source-bound receipt records the actual import closure and accepts only
`propext`, `Classical.choice`, and `Quot.sound`.
