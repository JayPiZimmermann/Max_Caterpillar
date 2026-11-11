# Verified actual finite growing-matching transfer

`GrowingMatching.conditional_finite_transfer` in
`MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/ConditionalBound.lean`
proves the finite inequality (T) from `TRANSFER.md` for an actual
translation-normalized homogeneous real skip network computing `MAX_(m+k)`
on every real input. All original first/outer indices and actual coefficients
are retained.

The hypotheses are the local structural statement `H(k,q)`, positive `k,q`,
and the numeric cutoff requirements `m≥2`, `4≤m+k`, `4≤K`, `K<m`.
These are weaker than the originally proposed `m≥400`, `k≥max(3,2q)`,
`4≤K≤m/100`. There is no assumed generic scale, rank estimate, event cover,
survival probability or counting prerequisite.

Write `n=m+k`, `c=7K/[24m(m−1)]`, let `M` count all original first rows whose
support has cardinality at least three, and let `L=Σⱼ (|supp Aⱼ|)_4`.
The conclusion is exactly

```
1 − 8K/m − M (k)_3/(n)_3
  − L/(n)_4 [K²(1+k/m)/(1−K/m) + (k)_2 K/2]
≤ h₂ (k)_(2q)/(n)_(2q) (c^q)⁻¹ exp(c k(n−1)).
```

The proof constructs one common actual gap scale, then proves a literal
cover by the internal-support event, short-isolated-rank event, actual
support-bad event, and original-neuron clean-survival/selected-matching
events. Each fraction is bounded using the independent actual-model
producers. A finite union/cardinality argument finishes the result. The
selected graph probability retains its `q!` until the exponential-series
bound cancels it; no independence between selected and complementary graph
edges is assumed.

`verification/h2/GrowingConditionalBoundCheck.lean` expands `H(k,q)` into its
actual finite-network statement and expands the rate `c`. It independently
checks the finite formula and the five major transitive axiom sets. The
known `H(5,2)` instance is checked, and an actual normalized `MAX10` network
is constructed for admissible `k=5,m=5,K=4`. This last control verifies
satisfiability; it does not claim positivity of that instance's left side.

The structural hierarchy for growing `q` remains unproved. Thus the result
is a verified **conditional transfer**, not an unconditional exponential
network lower bound. The proved quadratic affine-skip feeding-width theorem
remains a separate unconditional result.

Reproduce with
`python3 research/sN/jensen_bound/growing_conditional_recheck.py --run`.
