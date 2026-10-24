# One exponential count for caterpillars, rooted stars, bounded degree and few out-leaves

Status: proof below (self-checked, numerically checked); Lean complete, sorry-free, axioms
`propext, Quot.sound, Classical.choice` only, in `MaxCaterpillar/Simplify/Unified.lean`
(616 lines) and `MaxCaterpillar/Simplify/UnifiedMain.lean` (232 lines), not imported by the
root. Statements and axioms: `UnifiedStatements.lean`, log `unified_statements.log`.

## Setting

Coordinates `x_0, …, x_{N-1}`, `σ = relu`, `N ≥ 3`. A **unit** is `U = σ(A)`,
`A(x) = Σ_o h_o x_o + Σ_{(i,j)∈M} σ(x_i − x_j)` with integer head `h` and pairs `M`; its
hinge graph `F` (edge `{i,j}` per pair) is a forest. `κ_o := h_o + #{j : (o,j) ∈ M}`.
Leaves of `F` (degree 1) come in three kinds:

* **pendant**: `κ = 0`;  **out-leaf**: `κ = 1`;  **fixed leaf**: `κ ∉ {0, 1}`.

For a vertex `v` put

    ω(v) := #{out-leaves adjacent to v} + [v has a neighbour of degree ≥ 2].

(`ω(v) ≤ deg v`; the second term is 0 exactly when the component of `v` is a star centred at
`v`, an edge, or `v` is isolated.)

## Theorem

Let `Δ ≥ 2`. Let `max_N = Σ_{k∈K₁} d_k U_k + Σ_{F∈K₂} e_F U_F + R` with `R` in the auxiliary
span, `U_k` caterpillar functions and `U_F` tree units with `ω ≤ Δ` at every vertex. Then

    C(N, m) ≤ (2Δ+2)^m (|K₁| + |K₂|)          for 3 ≤ m ≤ N,
    (2Δ+3)^N ≤ (N+1) (2Δ+2)^N (|K₁| + |K₂|)   for every N ≥ 3,

i.e. `|K₁| + |K₂| ≥ (1 + 1/(2Δ+2))^N / (N+1)`. (Lean: `unified_choose_le`,
`unified_exponential`.)

**Per-unit lemma.** A unit with forest hinge graph and `ω ≤ Δ` (`Δ ≥ 2`) passes at most
`m! (N−m)! (2Δ+2)^m` permutations with tie set of size `m` (`card_passes_le_unified`).

### Covered classes

| class | why `ω ≤ Δ` | base `2Δ+2` |
|---|---|---|
| reduced forest of degree `≤ Δ` (`exponential.md`) | out-leaves and degree-≥2 neighbours are non-pendant (`omegaLe_of_redDeg`) | `2Δ+2` (same) |
| caterpillar functions (paper `U_k`) | reduced degree `≤ 2` | 6 |
| rooted stars of Brunck et al. and all their faces | no reduced edge | 6 |
| hinge degree `≤ Δ` | `ω ≤ deg` | `2Δ+2` |
| `≤ s` out-leaves at every vertex (`coverage.md`) | `ω ≤ s+1` (`omegaLe_of_outLeafBound`) | `2s+4` |
| hub class `HubOK Δ` | `≤ Δ` out-leaves | `2Δ+4` |

So both earlier classes lie in one class: the reduced-forest class with the same base, the
out-leaf class with base `2s+4` instead of `16(s+1)/3` (better for every `s ≥ 1`; for `s = 0`
the unified base is 6 against `16/3`). Caterpillars + rooted stars + all faces: `7^N ≤ (N+1)6^N(|K₁|+|K₂|)`, all `N ≥ 3`, the constant of the paper.

**Not covered** (no locality count can cover it): the *out-star*
`σ(x_c − x_a + Σ_{l≠a,c} σ(x_l − x_c))`, whose `N − 2` leaves are out-leaves of `c`
(`ω(c) = N − 2`). It passes every locality whose tie set contains `a` and `c`, in every order
of the rest, i.e. a fraction `k(k−1)/(N(N−1))` of all `k`-localities, so `N²` out-stars pass
every locality (`coverage.md`). Likewise the double out-star and an in-star whose centre has
`κ ≥ 2` with many `κ = 1` leaves.

## Proof

Steps S1–S3 and S5 are those of `exponential.md`: a locality is a permutation `ρ` with tie
set `T` (`|T| = m`); the mixed difference kills the auxiliary span and is `±δ` on `max_N`, so
every `ρ` is passed by some unit, where *passing* means

    (a) every o ∉ T has exactly κ_o hinge neighbours above it (T is above everything);
    (s) every t ∈ T without hinge neighbour in T has κ_t ≠ 0;

and (S5) all passed `ρ` with tie set `T` orient `F − T` alike, so a matching `P` of edges of
`F − T` cuts their number to `≤ m!(N−m)!/2^{|P|}`. Fix one unit; let `y = 1/(2Δ+2)`.

**S4 (forced vertices).** For passed `T`: an isolated vertex is tied iff `κ ≠ 0`; a pendant
is tied iff its neighbour is (two adjacent pendants are both tied); a fixed leaf is always
tied (untied it would have `κ = #neighbours above ∈ {0, 1}`).

**S6 (covering relation).** Root the forest by an injective child map on its edges. Call
`v` *poor* if `deg v ≥ 2` and `v` has no out-leaf and no pendant neighbour; its *heir* is a
neighbour `u` that is the child of the edge `vu` (at most one edge at `v` has child `v`, so
an heir exists; heirs are injective since the child map is). Let `R` consist of

* every out-leaf with its neighbour, if that neighbour is not a pendant;
* every poor vertex with its heir.

Then (i) `R` lies in the reduced forest (no pendant endpoints); (ii) `deg_R(v) ≤ max(2, ω(v))
≤ Δ`: a leaf has `R`-degree `≤ 1`; a vertex of degree `≤ 2` has `R`-degree `≤ 2`; a poor
vertex has no out-leaf neighbour, so it has its heir edge and at most one edge from a poor
vertex whose heir it is; a non-poor vertex has its out-leaf edges and at most one heir edge,
coming from a poor neighbour of degree `≥ 2`, which is counted by the trunk term of `ω`;
(iii) every non-pendant non-isolated vertex has an `R`-neighbour, or a pendant neighbour, or
is a fixed leaf (case analysis: out-leaf / fixed leaf / degree `≥ 2` with an out-leaf
neighbour, a pendant neighbour, or neither = poor).

Let `Φ` be the non-pendant vertices with an `R`-neighbour or a pendant neighbour. By S4 and
(iii) a passed `T` is determined by `T ∩ Φ` (vertices outside `Φ`: isolated, pendants whose
neighbour is a pendant or lies in `Φ`, fixed leaves). Blocks: the stars of a star cover of
`R` (`1 ≤ j ≤ Δ` leaves by (ii)) and the lone vertices `{v}` of `Φ` with a fixed pendant
neighbour `p_v`. Given `A = T ∩ Φ`, a star chooses a centre–leaf edge if the centre and some
leaf are outside `A`; a lone `v ∉ A` chooses `v p_v` (`p_v` untied by S4, private to `v`).
Chosen edges form a matching `P(A)` outside `T`. Hence

    #passed ρ with |T| = m ≤ m!(N−m)! Σ_{T} 2^{−|P(T∩Φ)|}
                          ≤ m!(N−m)! y^{−m} Σ_{A⊆Φ} y^{|A|} 2^{−|P(A)|}
                          = m!(N−m)! y^{−m} Π_blocks W,

with `W_star(j) = (1/2 + y)(1+y)^j + y^j/2 ≤ 1` (`1 ≤ j ≤ Δ`, `y = 1/(2Δ+2)`, `Δ ≥ 2`;
`star_weight_le_one`) and `W_lone = 1/2 + y ≤ 2/3`. So each unit passes at most
`m!(N−m)!(2Δ+2)^m` permutations.

**Count.** `N! ≤ Σ_units #passed`, i.e. `C(N,m) ≤ (2Δ+2)^m |K|`; caterpillar functions are
tree units with reduced degree `≤ 2` (`caterpillarFunction_eq_upTree`), hence `ω ≤ 2 ≤ Δ`.
For the exponential form, `(c+1)^N = Σ_m C(N,m)c^{N−m}` with `c = 2Δ+2 ≥ 6`; terms `m ≥ 3` by
the binomial count, `m ≤ 2` by the quadratic count `N(N−1) ≤ 6|K|`.

**Abstract per-unit lemma** (`card_passes_le_cover`, reusable): for any symmetric `R` inside
the reduced forest with `deg_R ≤ Δ` (`Δ ≥ 2`) satisfying (iii), the unit passes at most
`m!(N−m)!(2Δ+2)^m` permutations. The reduced-forest route is the instance `R` = reduced
forest; the unified route is the instance above.

## Remarks

* **Why `2Δ+2` and not `2s+2` for `s` out-leaves.** The binding block is a star centred at a
  vertex `r` with `s` out-leaves plus one poor neighbour whose heir is `r` (`j = s+1` star
  leaves). At `y = 1/(2s+2)` its weight is `1.059` (`s = 2`), `1.001` (`s = 3`), `< 1`
  (`s ≥ 4`). The trunk term of `ω` charges exactly this. Base `2s+2` for the out-leaf class
  would need the exact order count of a star (`≤ 1/(j+1)` instead of `1/2`); the true bases
  are much smaller (hill-climbing: `≈ 1.4, 2.5, 2.8, 3.2` for `s = 0..3`, `coverage.md`).
* **No L1, no L2/L3, no `β`-trick.** The out-leaf route needed the tie-set reconstruction from
  `{κ ≥ 1}`, the child counting L2, a degree-2 matching L3 and a binomial generating function;
  here the single star-cover block argument of the reduced route suffices once the star cover
  is built from out-leaf edges and heir edges instead of the whole reduced forest.

## Adversarial self-check

1. *Heir exists and is not a pendant / out-leaf.* Poor `v` has `≥ 2` neighbours, at most one
   edge with child `v` (injectivity), so some neighbour is a child; it is not a pendant or an
   out-leaf because `v` has none. A fixed leaf can be an heir; it is in `Φ` then (fine: it is
   a star member that is always tied, so its block never chooses an edge through it). ✓
2. *Heir injectivity.* `heir v = heir v' = h`: the pairs `{v,h}`, `{v',h}` both have child
   `h`, so they are equal, so `v = v'`. ✓ (Lean `heir_inj`.)
3. *`R`-degree of a degree-2 vertex with two out-leaf neighbours* (component = path
   `l–v–l'`): `ω(v) = 2`, `R`-degree 2. ✓ *Degree-≥3 out-leaf impossible.* ✓
4. *A non-poor vertex receives an heir edge only from a poor neighbour*, which has degree
   `≥ 2`, so the trunk term is 1; at most one such neighbour (injectivity). ✓
5. *Cover (iii).* Free `v` without pendant neighbour: degree 1 ⇒ out-leaf (then `R`-edge to its
   non-pendant neighbour) or fixed leaf (`κ = 0` would make it a pendant); degree `≥ 2` ⇒
   out-leaf neighbour (`R`-edge) or poor (heir edge). ✓
6. *Injectivity of `T ↦ T ∩ Φ`.* A pendant whose neighbour `v` is not a pendant: `v ∈ Φ`
   because `v` has a pendant neighbour. Free vertices outside `Φ` are fixed leaves (iii),
   always tied. ✓ (Lean `tie_eq_of_inter_block`.)
7. *Matching.* Blocks are disjoint subsets of `Φ`; lone edges use a pendant (not in `Φ`) whose
   unique neighbour is the lone vertex. ✓
8. *Class containment.* Reduced degree `≤ Δ` ⇒ `ω ≤ Δ` also at pendants (`ω ≤ deg = 1`). Out-leaf
   bound `s` ⇒ `ω ≤ s + 1`. Out-leaf definitions agree (`(incid M u).card = 1` vs one
   neighbour: equal under `i < j`, `card_incid_le_nbrs`). ✓
9. *Forest needed* for S5 (orientation determined by up-counts) and for the child map;
   `TreeFace` provides both (`descr_leaf`, `child`). ✓
10. *`N ≥ 3`, all `N`.* Exponential form via the quadratic count (`mixed_quadratic`), no
    threshold on `N`. ✓

## Numerical checks

* `unified_exh.c` (with `unified_exh.py` forest lists): **exhaustive** over all forests on
  `n ≤ 6` vertices up to isomorphism and all `κ_v ∈ {−1, …, deg v + 1}` (113 129 instances at
  `n = 6`): `Σ_T y^{|T|} q(T) ≤ 1` at `y = 1/(2Δ+2)`, `Δ = max(2, max ω)`, with exact order
  counts `q`; `max_{m ≥ 3} Σ_{|T|=m} q(T)/(2Δ+2)^m ≤ 0.037`. Also with `Δ = s+1` (out-leaf
  parameter): no failure.
* `unified_proof_check.py`: every proof step (R-degree, cover (iii), injectivity, chosen edges
  untied and disjoint, block weights) on random forests `n = 5, 6` and hill-climbing
  (maximising `Σ_T y^{|T|} q(T)`) at `n = 7` (10 × 150 steps) and `n = 8` (6 × 80 steps):
  no failure (`unified_climb7.log`, `unified_climb8.log`); exhaustive for `n ≤ 5` over all
  rootings (`unified_exh_proof.py`, `unified_exh_proof.log`).

## Lean status

`MaxCaterpillar/Simplify/Unified.lean` (616 lines): `IsOLeaf`, `IsFixLeaf`, `trunkDeg` (= `ω`),
`OmegaLe`, `fix_mem_tie`, `blockSet`, `tie_eq_of_inter_block`, **`card_passes_le_cover`**
(abstract per-unit lemma), `IsPoor`, `kids`, `heir`, `URel`, `heir_spec`, `heir_inj`,
`uRel_radj`, `uRel_deg`, `uRel_cover`, **`card_passes_le_unified`**.
`MaxCaterpillar/Simplify/UnifiedMain.lean` (232 lines): `omegaLe_of_redDeg`,
`card_incid_le_nbrs`, `omegaLe_of_outLeafBound`, `treeFace_card_passes_le`,
**`unified_choose_le`**, **`unified_exponential`**, `caterpillar_unified_exponential`,
`brunck_unified_exponential`, `hingeDeg_unified_exponential`, `outLeaf_unified_exponential`.
Build: `scripts/lean_lock.sh lake build MaxCaterpillar.Simplify.UnifiedMain`.

Reused: `StarCover`, `BlockSum`, the S4 lemmas of `Reduced` (`pend_mem_iff`, …), `TreeFaceR`
lemmas of `TreeUnits` (`redDeg_of_*`), `Brunck` (`caterpillarFunction_eq_upTree`,
`IsBrunckExpansion`), `CoverageMain` (`choose_le_of_unit_bound`, `pow_le_of_choose_le`,
`mixed_quadratic`, `OutLeafBound`).

Superseded (not used by the new files): `card_passes_le_red` (its proof is a copy of
`card_passes_le_cover`; it is the instance `R = RAdj`), `choose_le_of_red`,
`tree_reduced_choose_le/_exponential/_exponential_two`, `eventual_pow_le_of_choose_le`,
`seven_pow_le_of_choose_le'`, `brunck_expansion_choose_le/_exponential`; all of
`Coverage.lean` except the definitions `IsOutLeaf`, `OutLeafBound`
(`card_dpasses_le_of_outLeaf`, L1–L3, `exists_matching_of_leaf`, generating function), and
`tree_outLeaf_*`, `mixed_outLeaf_*`, `outLeafBound_of_*` in `CoverageMain`.
