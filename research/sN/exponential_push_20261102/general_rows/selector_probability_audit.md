# Independent audit of the selector probability calculation

**Verdict: the proposed counting and sufficient-cherry estimate are sound, with an explicit finite-size qualification.** This audit checks only sampling, rank ordering and the actual definition of isolated gaps. It does not certify the separate network-survival or literal-Good implication.

Write `m=N−7`. The four fixed labels `a,b,z,t` are distinct and disjoint from a set `P` of size `r`. A uniform seven-set containing `a,b`, excluding `z,t`, and containing exactly one label of `P` has probability

    s_N = r choose(N−r−4,4) / choose(N,7).

After conditioning on any such selected set, exactly `r−1` labels of `P` remain among the `m` tail labels. Thus the probability that the first tail position belongs to `P` is `(r−1)/m`. Conditional on this first-position event, `z,t` occupy an ordered uniform pair of distinct positions among `2,...,m`; this remains true after averaging over which P label came first. This requires `r≥2` for a nonzero event, and `N−r−4≥4` for a feasible selection. If either fails, the corresponding probability is zero.

## Gap indexing and the exact rank event

Use human tail positions `1,...,m` and human gaps `1,...,m`: gap 1 is between the selected anchor block and the first tail position; gap j, for j≥2, separates tail positions j−1 and j. Thus human gap 1 is exactly `Fin m` index zero in `GoodEventCherriesDefs.lean`. It is excluded from `isolatedGaps`, as intended.

If `z` occupies position `s` and `t` position `s+d`, with `s≥2` and `d≥2`, there are `d` intervening gaps, namely `s+1,...,s+d`. They are distinct from gap 1. For each fixed d there are `m−d−1` oriented placements, and `2≤d≤m−2`. The orientation is already included in this count; there is no additional factor 1/2.

Let H be the zero-based rank of human gap 1 under a uniform rank permutation. With K lowest ranks selected, the exact probability that H exceeds the ranks of all d intervening gaps and H≥K is

    p_d = [1−(K)_(d+1)/(m)_(d+1)]/(d+1).

Indeed, the distinguished rank is the unique maximum of these d+1 ranks with probability 1/(d+1). Their unordered rank set is uniform, and the event that its maximum is below K has probability `(K)_(d+1)/(m)_(d+1)`. The formula remains valid when K<d+1 by setting the numerator falling factorial to zero. It assumes 0≤K≤m; the useful lower bound assumes K<m. Since the all-low probability is at most K/m,

    p_d ≥ (1−K/m)/(d+1).

Consequently the proposed base event probability, before imposing EnoughCherries, is exactly

    s_N * (r−1)/m / [(m−1)(m−2)]
      * Σ_(d=2)^(m−2) (m−d−1)/(d+1)
          * [1−(K)_(d+1)/(m)_(d+1)].

For `r/N→α∈(0,1)` and `K/m→δ<1`, its leading asymptotic is

    [210 α²(1−α)^4 + o(1)] log(N)/N³.

Here `s_N ~ 210 α(1−α)^4/N²`. The uncorrected sum is exactly `m H_(m−1)−5m/2+3`; the falling-factorial correction is O(m), since its dth factor is at most `(K/m)^(d+1)`. Therefore the logarithm's leading coefficient is one, independent of fixed δ<1. Using only the lower bound for p_d proves the weaker but sufficient leading constant multiplied by `(1−δ)`.

## Retaining the actual EnoughCherries event

Let Γ be the K-element set of lowest-ranked gaps, let ν count adjacent pairs of selected gap indices along the path on `0,...,m−1`, and let `Q=|isolatedGaps Γ|` use the production definition. The production geometry already proves

    Q ≥ K−1−2ν.

The minus one accounts for the excluded anchor gap. The final gap is retained when isolated; no second boundary loss is needed. If `Q<K/2` and `K≥4`, then `ν>K/4−1/2≥K/8`. A path with ν edges has a matching with at least ν/2 edges, so Γ contains endpoints of a matching of size at least K/16. Put `t=floor(K/16)`; for K≥32, `t≥K/32` and t≥1.

A fixed matching of t path edges has 2t distinct endpoints. Its probability of being contained in a uniform K-subset is `(K)_(2t)/(m)_(2t)≤(K/m)^(2t)`. There are at most `choose(m,t)` such matchings, hence

    P(Q<K/2) ≤ choose(m,t)(K/m)^(2t)
              ≤ [32 e K/m]^t
              ≤ [32 e δ]^t ≤ 2^(−t)

when `K≤δm` and `δ≤1/(64e)`; the proposed `δ≤1/256` satisfies this. This bound is valid for K≥32. Values 1≤K<32 need a separate estimate or may simply be omitted from an eventual asymptotic claim. For K=0, EnoughCherries is automatic.

## Where to subtract the failure probability

Q depends only on the rank permutation, which is independent of the selected set and tail permutation. Q need not be independent of the distinguished-rank witness. Conditional on the selected-set event and first-P event, write `b_(m,K)` for the oriented-placement/rank probability given by the sum above, and `ε=2^(−floor(K/16))`. The valid lower bound is

    P(base event ∩ EnoughCherries)
      ≥ s_N * (r−1)/m * [b_(m,K)−ε].

It comes from subtracting `P(Q fails)≤ε` inside this conditional experiment. Subtracting ε globally would be unnecessarily weak. Multiplying by `(1−ε)` would unjustifiably assert independence and is not valid from this argument.

For every fixed δ>0, `ε=exp(−Ω(m))=o(log(m)/m)`, so imposing EnoughCherries preserves the displayed leading asymptotic constant. **K≥32 alone does not guarantee that the bracket is positive.** For a finite statement, retain the exact bracket or add an explicit growth threshold; for example `K≥64 log₂m` gives `ε≤m^(−2)` using `t≥K/32`, which is negligible compared with the main term. This additional threshold holds eventually for `K=floor(δm)` with fixed δ>0.

## Independent finite checks

`selector_probability_check.py` verifies the rank formula by full permutation enumeration for m=4,...,8 and all K=0,...,m; checks the production isolated-gap convention and matching deductions for every subset of paths with m≤16; and independently counts seven-set selections for N=8,...,16. Its JSON result records these exact checks separately from floating asymptotic diagnostics. These computations support the elementary arguments above; they are not Lean theorems and do not check the network semantics.

## Enlarged event: no first-tail-P condition is needed

The construction audit subsequently identified that its required inequality for the tail coordinates holds regardless of the first tail label. Taking that separate semantic observation as given, the first-tail-P restriction may be dropped entirely. The probability calculation becomes simpler and strictly enlarges the event above. The selection event and its probability s_N are unchanged, but the factor `(r−1)/m` disappears. In particular r=1 is no longer excluded by this count.

Now `z` may occupy any human tail position `s≥1`, with `t` at `s+d` and `d≥2`. The intervening human gaps are still `s+1,...,s+d`, so even when s=1 they start at gap 2 and exclude the anchor gap 1. The same rank formula p_d therefore applies, including the new endpoint d=m−1. There are now `m−d` oriented placements for each d, out of `m(m−1)` ordered distinct placements. Thus, for m≥3, define

    btilde_(m,K) = 1/[m(m−1)]
      * Σ_(d=2)^(m−1) (m−d)/(d+1)
          * [1−(K)_(d+1)/(m)_(d+1)].

The exact enlarged base probability is `s_N*btilde_(m,K)`, with no first-label condition. There is again no extra factor 1/2: only the desired orientation is counted in `m−d`. At the endpoint d=m−1, all m gap ranks occur in the comparison, so p_d=1/m for K<m, agreeing with the distinguished anchor rank being globally largest.

The uncorrected sum now equals

    (m+1)H_m−5m/2+1/2.

For `K/m→δ<1`, its falling-factorial correction is O(m) by the same geometric bound. Hence

    s_N*btilde_(m,K)
      = [210 α(1−α)^4+o(1)] log(N)/N³

when `r/N→α∈(0,1)`. This coefficient is maximized at α=1/5 and then equals 17.2032. The enlarged probability is larger than the previously restricted event, whose exact count and checks above remain valid.

The actual sufficient-cherry bound is unchanged. Independence of the selected set from the rank permutation, without any independence between the rank witness and Q, gives

    P(enlarged base event ∩ EnoughCherries)
      ≥ s_N * [btilde_(m,K)−ε],

where `ε=2^(−floor(K/16))` under the conditions already stated. Thus EnoughCherries preserves the enlarged leading coefficient for every fixed `0<δ≤1/256`. The same finite-size caution applies: do not claim positivity solely from K≥32. Retain the exact bracket, or add a threshold such as `K≥64 log₂m`.

The independent script now preserves all original checks and additionally enumerates every rank permutation for m=3,...,8, d=2,...,m−1 and K=0,...,m, with interval indices `1,...,d` in zero-based indexing. It also directly enumerates every oriented pair of tail positions and every rank permutation for m=3,...,7, comparing the resulting joint fraction with btilde. This explicitly checks the new first-tail-position and maximal-distance cases and the placement normalization. The new asymptotic floating diagnostics are reported separately; they do not verify the semantic reason for removing the first-tail restriction.
