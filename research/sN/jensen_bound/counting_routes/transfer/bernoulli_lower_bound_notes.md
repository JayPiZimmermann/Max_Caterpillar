# Verified actual Bernoulli conditional square-root exponential bound

The actual normalized-model theorem is
`GrowingMatching.Bernoulli.conditional_sqrt_lower_bound` in
`GrowingMatching/Bernoulli/LowerBound.lean`. Let `d≥1` be an integer and
`n≥10^10 d²`. For an actual translation-normalized homogeneous real skip
network computing `MAX_n` on every real input, let

```
M = #{j : |supp A_j|≥3},
L = Σ_j (|supp A_j|)_4.
```

These statistics include **all** original first rows, including output-only
rows. If `M,L≤d² n²` and the literal local structural hypothesis below holds,
the theorem proves

```
h₂ ≥ (1/2) exp(3 sqrt(n)/(8000d)).
```

The structural hypothesis is `H(k₀,q)` at the literal choices

```
q  = floor((sqrt(n)/(1000d))/8),
k₀ = 4q+1.
```

It says that every actual finite translation-normalized braid-first MAX_k₀
skip network has an original outer preactivation whose aggregate interaction
graph contains a q-edge matching. This contains no random-restriction,
probability, rank or lower-bound conclusion. Its growing levels remain
**unproved**. Consequently the displayed exponential result is conditional,
not an unconditional exponential lower bound.

The finite actual-model bridge is
`GrowingMatching.Bernoulli.finite_conditional_bound` in `ConditionalBound.lean`.
It derives one common positive generic scale over every actual selected set
and raw tail/rank permutation. The original-neuron witness is obtained after
upward arity monotonicity of H. Sets smaller than k₀ pay their literal size
failure indicator. All other configurations are covered by the intrinsic
short-rank event, the actual role-based support-bad event, or an original
second-neuron event. The latter requires actual cleanliness, actual inner
zero at the same original-coordinate point, and an actual selected q-matching.

The selected set follows the genuine Bernoulli product weights, conditioned
on no original nonbraid support being internal and on the literal cap
`|S|≤floor(2np)`. This is a downward event with proved positive mass. Harris
domination bounds selected-label and matching events without an inverse
conditioning-mass penalty. Only the small-cardinality tail pays that mass;
its Chernoff exponent dominates the explicitly bounded support-avoidance
penalty. This avoids the fixed-cardinality union-bound restriction that
previously forced selected arity to the cube-root scale at quadratic support
budgets.

With

```
p = 1/(1000d sqrt(n)),
K = floor(n/(1000d²)),
```

the independently verified parameter package proves all floors, tail lower
bounds, positive denominators, event budgets and the neuron envelope.
The final theorem has **no** common-scale, genericity, event-cover, survival,
conditional-mass, probability, rank or counting hypothesis. Only actual model
exactness/normalization, the actual geometric M/L budgets, numeric n/d bounds,
and the explicit structural H remain. A separate raw affine-skip half-model
wrapper derives the M/L budgets from original quadratic first width.

`verification/h2/BernoulliLowerBoundCheck.lean` expands H, the literal matching
parameters, and the actual support statistics. It independently checks the
whole theorem and five major transitive axiom sets. Numeric parameter
feasibility at `(n,d)=(10^10,1)`, the separately proved low instance `H(5,2)`,
and an actual normalized `MAX10` construction are distinct controls. They do
**not** provide a joint witness of the open growing-H premise at the literal
large choices.

Reproduce the whole normalized gate with
`python3 research/sN/jensen_bound/bernoulli_lower_bound_recheck.py --run`.
Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
