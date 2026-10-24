# h4-any-network, round 3: locality method beyond caterpillar second layers

## Live claim (top)

**Theorem CVX (proved on paper, checked numerically).** Let `N ≥ 4`. Suppose
`max_N = Σ_{k∈K} d_k σ(g_k) + R` on the open positive orthant, where `R` is a
finite sum of functions each depending on at most two coordinates (e.g.
`R ∈ A_N`), and every second-layer preactivation `g_k` is a *convex braid
function*: `g_k = ℓ_k + Σ_{i≠j} c_{k,ij} σ(x_i − x_j) + Σ_i (a_{k,i} σ(x_i) + b_{k,i} σ(−x_i))`
with `ℓ_k` linear, arbitrary reals `a, b`, and `c_{k,ij} + c_{k,ji} ≥ 0` for
every pair (equivalently, `g_k` is convex on the positive orthant).
Then `|K| ≥ N(N−1)/9`, and in fact `|K| ≥ N(N−1)/6` for every `N ≥ 3`
(the base case `F(5) ≤ 3` is proved by the case analysis in Lemma P4 below;
`N = 4` uses integrality: `|K| ≥ 4/3`).

This contains every caterpillar expansion (head + Σ_M σ(ℓ), coefficients +1) and
drops integrality, normalization, the caterpillar shape and the apex property.
The paper's Lean theorem gives `N(N−1)/6` for caterpillars.

**CVX6 (now proved on paper via P4; double-check the case analysis before
Lean).** `F(n) ≤ n−2` for `n ≥ 5`. Evidence besides the proof: exhaustive integer weights 0..2 at N=5 (the 0..3 run was aborted unfinished), unit weights at N=6 (all 156 graphs),
sampled N=6 (weights ≤2) and N=7: max `f` equals `N−2` in every run. Measured.

**Proposition STAR (proved on paper, checked by direct evaluation).** The
locality count cannot prove more than `O(N²)` for convex second layers and
`O(N)` for unrestricted braid second layers. Witnesses below.

## Survey of exact known results (two hidden layers, exact representation)

- Safran, COLT 2026 (PMLR 336, arXiv:2601.01417), Thm 2.1: a depth-3 (two hidden
  layers) network equal to `Max_d` on `[0,1]^d` has width (max layer width) at
  least `(1/8 − 1/(4d) − 1/(2d²)) d²`. Thm 1.1: depth `k`, `3 ≤ k ≤ log2 log2 d`,
  width `≥ 0.1 d^{1+1/(2^{k−2}−1)}`. Mechanism: missing first-layer pair
  supports + Turán, coordinate freezing.
- Lu, "Sharp closure thresholds…" (Zenodo 10.5281/zenodo.22728502, v1 2026),
  Thm 2.13: exact two-hidden-layer realization needs first width
  `r_ex(d) ≥ C(d,2) − ⌊4d/3⌋` (d ≥ 4); Prop 7.1 paired-core reduction
  (homogenize, freeze, every 3-set contains a first-core support); decoder
  (second width) size explicitly left open (his construction: `exp(O(d log d))`).
- Grillo–Hertrich–Loho, NeurIPS 2025 (arXiv:2502.09324): for networks
  compatible with the braid fan (every neuron), `Ω(log log d)` hidden layers are
  needed for `max_d`; under the same assumption three hidden layers are
  necessary for `max_5`. Hence two-hidden-layer braid-fan-compatible networks
  do not represent `max_N` for `N ≥ 5` at all: second-width bounds are vacuous
  there. (Our "braid first layer" class only restricts the first layer and
  contains the Caterpillar Net.)
- Hertrich–Basu–Di Summa–Skutella, Prop. 2.3; Haase–Hertrich–Loho, Lemma 7:
  biases can be removed for positively homogeneous targets (same widths).
- Upper bounds: BSY arXiv:2610.28587 (two layers suffice for all CPWL);
  Caterpillar Net widths `C(N,2)+N+1`, `2^{O(N log N)}`; Ruess et al.
  (arXiv:2607.21651, N ≤ 12), Wang–Basu (arXiv:2608.25221, N ≤ 8).
- No lower bound on the *second* width of general two-hidden-layer networks
  for `max_N` was found in these sources beyond what follows from the first
  width; the first width is forced to be quadratic by Safran/Lu.

## Setting and the general locality lemma

Locality `(T,ρ)`, `|T| = m ≥ 3`: open cell
`C_{T,ρ} = {x_t = s ∀t∈T, s > x_{ρ1} > … > x_{ρ(N−m)} > 0}`.
Lemma L (proved). Pick `p ∈ C_{T,ρ}` avoiding the finitely many hyperplanes
`{g_k = 0}` of neurons not identically zero on the cell, and `δ` small. The
m-th mixed difference `Λ` in the `T` coordinates on the cube of side `δ` at `p`
kills `R`, linear functions, `σ(±x_i)` (linear on the orthant), every neuron
with `g_k(p) ≠ 0` (locally linear plus hinges inside `T` or zero), and gives
`Λ max_N = ±δ`. So some `k` with `g_k ≡ 0` on `C_{T,ρ}` has `Λ σ(G_k) ≠ 0`,
where `G_k(z) = g_k(p+z)` is the germ: we say `k` *sees* `(T,ρ)`. The base-B
digit argument of the paper is replaced by genericity, so real coefficients
are allowed.

Normal form on the orthant: `g = Σ γ_i x_i + Σ_{e} c_e max(x_i, x_j)`,
`c_e = c_{ij} + c_{ji} ≥ 0`. Put `deg(x) = Σ_u c_{xu}`, `Γ_x := γ_x + deg(x)`
(generalizes κ). For `m = 3`, `(T,ρ)` is seen iff
- (a) every `o ∉ T` has up-weight (weight to neighbours above it, `T` above all
  of `O`) equal to `Γ_o`;
- (c) `Σ_{t∈T} Γ_t = c(E(T))`;
- (Λ) `Σ_{t∈T} [σ(Γ_t) − σ(d_t − Γ_t)] ≠ 0`, `d_t = c(t, T∖t)`.
Proof: `g|cell` is linear in `(s, x_O)`; its `x_o`-coefficient is
`γ_o + Σ_{u∈O below o} c_{ou}`, its `s`-coefficient is
`Σ_T γ_t + c(T,O) + c(E(T))`; germ `G(z) = Σ v_t z_t + Σ_{e⊂T} c_e max(z_e)` with
`v_t = Γ_t − d_t`; (c) gives `G(z+λ1) = G(z)`, so `G(1_{T∖t}) = G(−e_t) = d_t − Γ_t`
and `G(e_t) = Γ_t`, and the 8-corner sum collapses to (Λ). The closed form is
re-checked against the brute 8-corner sum inside `convex_m3.cpp` (abort on
mismatch; none).

## Proof of Theorem CVX

Define for a weighted graph `H` on `n ≥ 3` vertices (`c ≥ 0`) and `Γ ∈ R^V`:
`W(H,Γ)` = number of pairs (3-set `T`, order of `V∖T`) satisfying (a),(c),(Λ);
`f = W/(n−3)!`; `F(n) = sup f`. A neuron sees `W·1` localities of the
`C(N,3)(N−3)!`, so `|K| ≥ C(N,3)/F(N)`.

P1 (peeling). For `n ≥ 4`: `W(H,Γ) = Σ_{b∈R(H)} W(H−b, Γ|)`, where
`R(H) = {b : Γ_b = deg_H(b)}`. [The bottom vertex `b` of `O` has all
neighbours above, so (a) at `b` reads `Γ_b = deg(b)`; deleting `b` changes no
other up-weight, nor (c), nor (Λ).] Hence `f(H) = (1/(n−3)) Σ_{b∈R} f(H−b)`.

P2 (almost all removable). If `|R| = n`, `W = 0`. If `R = V∖{u}`, then
`f ≤ max(n−2, 3)`. [If `T ⊆ R`: (c) becomes `Σ_T deg = c(E(T))`, i.e. no edge
meets `T`, so all `d_t = 0` and (Λ) fails; so `u ∈ T = {u,a,b}`. Every `o∈O`
has up-weight `deg(o)`, so `H[O]` has no edge and all of `O`'s orders work;
every edge meets `T`. From (c), `Γ_u = −c_{ab} − c(a,O) − c(b,O) ≤ 0`, and
(Λ) evaluates to `c_{ab}`. So seen `T` ↔ edges `ab` of `H−u` covering `H−u`.
Covering edges pairwise intersect, hence form a star (≤ n−2 edges) or a
triangle (3).]

P3 (induction). `F(3) ≤ 1`; `F(4) ≤ 3` (P1 gives `f ≤ |R|`, P2 for `|R| ≥ 3`);
for `n ≥ 5`: if `|R| ≤ n−2`, P1 gives `f ≤ |R| F(n−1)/(n−3)`; else P2. With
the hypothesis `F(n−1) ≤ (3/2)(n−3)` this gives `F(n) ≤ (3/2)(n−2)`. Hence
`|K| ≥ C(N,3)/((3/2)(N−2)) = N(N−1)/9`. If `F(5) ≤ 3` (CVX6 base), the same
induction gives `F(n) ≤ n−2` for `n ≥ 5` and `|K| ≥ N(N−1)/6`.
`F(4) = 3` is attained (triangle plus an isolated vertex with Γ = −3), so the
induction cannot start at 4 with constant 1.

P4 (`F(5) ≤ 3`). Only `|R| = 3` needs work (`|R| ≤ 2`: `f ≤ ½·2·F(4) = 3`;
`|R| ≥ 4`: P2). Let `R = {r1,r2,r3}`, non-removable `u1,u2`,
`δ_i = deg(u_i) − Γ_{u_i} ≠ 0`. Any seen locality forces `ΣΓ = c(H)`, i.e.
`δ1 + δ2 = c(H)`. By P1, `f = Σ_P (#valid orders of P)/2 · [V∖P seen]` over
pairs `P = O`. Valid: `P ⊆ R` nonadjacent (weight 1), or `P = {r,u_i}` with
`c_{r u_i} = δ_i > 0` (`r ∈ A_i`, weight ½); nothing else. Distinct A-edges
give `Σ|A_i|δ_i ≤ c(H) = δ1+δ2`; if some `A_i ≠ ∅` both `δ > 0`, leaving
`(|A1|,|A2|) ∈ {(0,0),(1,0),(1,1),(2,0),(3,0)}` up to symmetry. Using
`Λ = Σ_T clamp(Γ_t,0,d_t) − c(E(T))` and `Γ_r = deg(r)` (clamp = `d_r`):
(1,1): no other edges, every candidate has `Λ = 0`, `f ≤ 1`.
(1,0): `{r_a,u1}` is seen iff `c_{r_b r_c} > 0`, which kills pair
`{r_b,r_c}`: `f ≤ 2.5` or `≤ 3`.
(2,0),(3,0): `Γ_{u2} < 0`, `Γ_{u1} ≥ d_{u1}`; `{r_i,u1}` is seen iff
`c_{r_j r_k} > 0`, and pairs inside `R` need non-edges, so
`f ≤ (3 − e) + e/2 ≤ 3` with `e` the number of edges inside `R`.

## Proposition STAR (limits of the method)

- Signed star, any braid first layer:
  `U = σ(Σ_{p∈P} σ(x_p − x_0) − Σ_{q∈Q} σ(x_q − x_0))`.
  At a locality with `0 ∈ T`, `|T∩P| = p`, `|T∩Q| = q`: `Λ U = (−1)^m δ F(p,q)`,
  `F(p,q) = Σ_{i,j} (−1)^{i+j} C(p,i) C(q,j) σ(i−j) = −C(p+q−2, p−1)` for
  `p,q ≥ 1` (Pascal in `q` turns `σ(i−j)` into `[j ≤ i−1]`, partial alternating
  sums give `(−1)^{i−1}C(q−2,i−1)`, then Vandermonde). With a balanced split
  `U` sees all localities with `0 ∈ T` meeting both `P` and `Q`: a fraction
  `≈ (m/N)(1 − 2^{2−m})`. For `m=3` the counting bound is at most
  `C(N,3)/(⌊(N−1)/2⌋⌈(N−1)/2⌉) ≈ 2N/3`. For `m = 3`, `T = {0,p,q}` the germ is
  exactly `max_3 − max(z_0,z_q)`, i.e. the full class of `max_3`.
- Convex star: `U = σ(−2(x_f − x_s) + σ(x_f − x_s) + Σ_{ℓ≠s,f} σ(x_ℓ − x_s))`
  sees every locality with `s, f ∈ T`: `C(N−2,m−2)(N−m)!` localities, so the
  method gives at most `N(N−1)/(m(m−1))` for convex second layers; `m = 3` is
  optimal and Theorem CVX is within a factor 3/2 of this ceiling. This is the
  NOTE's "abstract star with κ ≡ 1": leaves with κ = 1 are exactly what the
  caterpillar shape forbids, which is why the exponential bound needs it.
- Both counts confirmed by direct exact evaluation of the full neurons at the
  paper's base points, N = 4..7, all m (`star_direct.py`, `star_direct.log`;
  the signed star sees slightly more than predicted for even m, from
  localities with `0 ∉ T`; the claim is a lower bound on what it sees).

## Failed routes / reopening conditions

- Exponential bound for convex (positive-hinge) second layers by locality
  counting: refuted by the convex star (ceiling `N(N−1)/6`). Reopen only with a
  functional that sees more than one corner class (e.g. full germ classes mod
  functions of fewer variables, or rank arguments across localities).
- Any super-linear bound for unrestricted braid second layers by single-m
  locality counting: refuted by the signed star. Reopen with a rank/linear
  algebra argument over localities, not a per-neuron count.
- Arbitrary first layer: at a generic point of `Φ_T` the first-layer neurons
  with support exactly `T` (and zero sum) survive `Λ`; there are at most `h_1`
  such `T`, so for `C(N,m) > h_1` "clean" `T` exist, but a clean `T` only forces
  one seeing neuron, and stars still see `≈ m/N` of all localities. No
  `f(N)/poly(h_1)` bound obtained.
- Lemma "Pr over orders ≤ 1/2 per matched edge" for signed weights: false in
  general (cancellations); for nonnegative weights it holds via the
  orientation-uniqueness lemma (two acyclic orientations with equal weighted
  out-degrees differ on a positive circulation, which contains a directed
  cycle) — kept as a tool, not needed for CVX.

## Files and reproduction

- `star_identity.py` — table of `F(p,q)`; `star_direct.py` → `star_direct.log`.
- `convex_scan.cpp` (all m, unit weights, graphs up to iso) →
  `convex_scan_N6_R5.log` (N=4,5 printed in chat run: m=3 max 3 and 3).
- `convex_m3.cpp` (m=3, weights 0..W, exhaustive or sampled) →
  `convex_m3_N5_W2_all.log`, `convex_m3_N6_W2_s20000.log`,
  `convex_m3_N7_W1_s3000.log`, `convex_m3_N7_W3_s2000.log`,
  `convex_m3_N5_W3_all.log` (aborted, no result).
- `peel_check.py` → `peel_check.log`: exact-rational check of P1 and of
  `f ≤ (3/2)(n−2)` on 400 random instances, independent code path.
- Build: `g++ -O2 -o convex_m3 convex_m3.cpp`; run `./convex_m3 N W samples seed R`.
- Hashes in `SHA256SUMS.txt`.
