# Arbitrary first rows: can the seven-input obstruction force a superquadratic bound?

**Current conclusion (2 November 2026): a proposed raw constant-cubic transfer cost is refuted by a new actual random-scale selector family; no unconditional superquadratic NETWORK bound is established here. See SELECTOR.md for the audited logarithmic counterexample.** The actual transfer from the explicitly supplied seven-input `SC′₂` obstruction is exact; the missing step is an actual per-neuron cubic probability bound. Freezing its modular offsets is false even when *every* tail-prefix equation is zero. A new small exact family shows that a cubic raw bound, if true, is tight and that its witness can have nonzero top Möbius coefficient. This folder changes no production Lean source or root.

The local PDF is `notes/paper_simon_jensen.pdf`; the text read for this audit is `/tmp/paper_simon_jensen.txt`, Sections 6, 8 and 9. The previous boundary note is `research/sN/exponential_bound/sc2_arbitrary_transfer_audit.md`.

## 1. Exact transfer and its current trust boundary

Write `SC′₂(7)` for the following **explicit external structural hypothesis**: a normalized braid network on seven inputs computing MAX has some second preactivation whose Boolean quadratic is outside `C₂`. Here `C₂` is the union of quadratics anchored at at most two coordinates and quadratics whose interaction graph has vertex cover at most one. An anchor A means G(B)=0 for **every** B containing A. This is not the stronger, still-open `SC₂` hypothesis for all vertex-cover-two quadratics.

Sample a seven-set S, tail order τ and independent gap-rank order ρ. Use the one common actual gap scale supplied by the production Sampling theorem. On the complement of `Internal` (some original nonbraid support lies inside S), actual localization gives a braid model on S. Given `SC′₂(7)`, at least one original second index survives and has actual local G outside C₂. Thus for any further actual event E,

    P(E) − P(Internal) ≤ Σ_k P(E ∩ {k survives, actual G_k outside C₂}).

This is an ordinary finite covering implication; it does not freeze a modular vector. In particular E can be the completed literal Good event together with the sufficient-cherry event. The internal-row union bound is at most `M (7)_3/(N)_3` for M original nonbraid rows.

If a **new** uniform actual cost

    P(Good ∩ EnoughCherries ∩ {k survives, G_k outside C₂}) ≤ C_D / K³

were proved for arbitrary normalized first rows after the verified half restriction, `SC′₂(7)` would imply `h₂ ≥ c_D N³`. There is no additional logarithmic loss forced by our current machinery: the verified weighted fourth-support Good-event estimate uses L=Σ_j(|supp A_j|)_4, and the half restriction gives L=O_D(N²) when h₁≤D N². Set K=δ_D N to retain a fixed positive probability. The old audit's N³/log⁶N consequence used a maximum support cutoff and is superseded **as a conditional transfer calculation**, not as an established lower bound.

The displayed raw constant-cubic cost is now **refuted** by SELECTOR.md: actual survival with local G outside C₂ and both Good and EnoughCherries has probability Ω(log N/N³) even with O(N) support-at-most-four rows. A logarithmic or score-sensitive replacement could still yield a superquadratic transfer. Existing actual matching-coin estimates give only a quadratic upper cost.

## 2. Why every prefix equation still does not freeze the offset

The genuine normalized two-row preactivation

    g(x)=σ(x_a−x_b+x_z−x_t)−σ(x_z−x_t)

has one first row of support four and one braid first row. Take a seven-set containing a,b and five unused coordinates, excluding z,t. All selected coordinates are zero.

For any tail values z>t, both first rows have the same positive value at q, so g(q)=0 and the actual active-gate derivative is e_a−e_b. For z<t, both rows are inactive, g(q)=0 and the actual derivative is zero. Consequently **every tail coefficient and every tail-subset sum is zero in both cases**, hence all prefix equations hold. On a sufficiently small neighborhood in the selected variables the two actual local preactivations are y_a−y_b and zero. There are no internal first rows at either point.

`AdaptiveOffset.lean` checks this for an actual `NormalizedNetwork 9 2 1`, a literal seven-set, two literal tied-top points, the original active-gate derivative, exact neighborhood identities and all tail-subset sums. It also checks the generic original-network identity

    g(x)−g(−x)=2⟨U,x⟩+Σ_j W_j⟨A_j,x⟩.

That global odd part is fixed. The localized odd part need not be fixed. This counterexample refutes a shortcut in the transfer argument, **not** a cubic network lower bound or a cubic per-neuron cost. It is itself only a modular local example.

## 3. An O(N)-row sharp cubic control with genuine top interaction

Fix distinct a,b,c,z,t and let

    h(x)=Σ_{e≠a,b}[σ(x_e−x_a)+2σ(x_e−x_b)]
         +σ(x_c−x_a+x_z−x_t)−σ(x_z−x_t).

There are `2N−2` first rows, including just one nonbraid row of support four. Every row is zero-sum. Suppose S has size seven, contains a,b,c and excludes z,t. At every actual ordered gap point:

* h(q)=0 and every actual tail derivative is zero;
* the nonbraid row is not internal;
* if z<t, the local function is the anchored two-hub core;
* if z>t, its Boolean quadratic is

      G(B)=Σ_{e∈S\{a,b}} 1_e[(1−1_a)+2(1−1_b)]+1_c−1_a.

Its interaction graph is exactly K_{2,5}. The only vertex cover of size at most two is {a,b}, and G({a,b})=−1. Every anchor is a vertex cover, so G has no anchor of size at most two. It is outside C₂. This happens on the literal event above with probability

    choose(N−5,4)/(2 choose(N,7)) = (105+o(1)) N⁻³.

Therefore a uniform raw cubic cost would be sharp, even with this very small nonbraid dictionary.

This control is stronger than the even/dummy-variable degeneracy of the earlier Prop. 46 gadget. On n≥4 local coordinates the exact identity is

    max(G(B),0) = G(B) + 1{B={a}} + 1{a,b∈B, c∉B}.

Since G is quadratic, its top coefficient vanishes for n≥3; the last indicator has a free fourth coordinate and also has zero top coefficient. Hence

    μ_[n](G_+) = (−1)^(n+1),

in particular 1 at n=7. This does **not** assert that the individual neuron glues to a braid-linear function, or that an arbitrary SC′₂ certificate score is nonzero. The distinction matters.

`sharp_cubic_control.py` independently evaluates the original ReLU preactivation on 4,374 exact rational neighborhood inputs, checks the complete Boolean identity for n=4,...,9, checks the primitive no-anchor condition at n≥5, and records exact sampling probabilities. All checks pass in `sharp_cubic_control.json`. The all-N probability and Möbius formulas above are the elementary mathematical arguments, not additional finite computational certificates.

## 4. Certificate scores and reversal: a real boundary

Counting actual nonzero certificate scores Φ(G), rather than the raw event G outside C₂, might discard useless local neurons. But no such strengthened analytic estimate is proved here.

In particular μ₇(G_+)=0 for complement-symmetric G does not imply Φ(G)=0 for an arbitrary supplied certificate. Reversal sends G to its complement transform, preserving the interaction graph but possibly changing an anchor-two model into a nonanchored vertex-cover-two model. Thus a reversal-odd symmetrization of an SC′₂ certificate is not automatic: it could require the stronger open SC₂ statement. For the matching-number/vertex-cover classes that really are reversal-invariant, that symmetrization is legitimate, as the root's separate route observes.

The sparse-clique obstruction to the completed matching statistic also remains: selected K₄ inside a clique of size √N has probability Θ(N⁻²), while the observed low-cherry edge count has bounded mean. One must use additional prefix/gradient information or a stronger score criterion, rather than simply reweighting the same statistic.

## 5. Availability of the claimed SC′₂ certificate

Section 9.4 names

* `data/n7x_cert_6prime.json.gz`, 14,455,262 bytes,
* SHA-256 `3868b7786d5edbc870c6a0427fa6aaa0fcfd7817d073226a02aafa544b30e585`,
* verifier `tools/iv7_verify7.py`.

The supplied PDF's data-availability statement says the supplementary material will be archived with a DOI; it does not supply that archive link. None of these producer/verifier/data files is present under `/home/jzimmermann/code`. The current repository's closed five-input star certificate is a different object. Therefore this audit treats SC′₂(7) as an explicit hypothesis and does not describe its larger certificate as verified here.

## 6. Best next discriminating target

After the SELECTOR.md refutation of the raw constant-cubic cost, prove or refute a *score-sensitive joint* cubic cost, or an O(log N/N³) raw upper cost, for a full-support, certificate-relevant local quadratic, with the original real row coefficients retained. Require actual active-gradient tail vanishing; do not replace it by graph-only matching statistics, a fixed modular vector, or a conditional survival probability after Good. The adaptive two-row gadget and the O(N)-row sharp cubic control above should be regression tests. A proof must recover an additional selected witness at cost N⁻¹ despite its adaptive offset, or exploit more of the original gradient's prefix-zero equations. No proof of that step has been found in this run.
