import MaxCaterpillar.Retained
import MaxCaterpillar.Count.Main
import MaxCaterpillar.Competing.Support
import MaxCaterpillar.Dimension

/-! # The public theorem interface

The objects are defined in `Definitions.lean`, `Count/Defs.lean` (tree face functions and
the class `ω ≤ Δ`) and `Competing/Defs.lean` (the construction of Brunck et al.).

* `caterpillar_net`: the Caterpillar Net computes `max_N` with two hidden
  layers of widths `firstWidth N` and `secondWidth N`, rational weights, and
  zero biases.
* `unified_choose_le`, `unified_exponential`: every expansion of `max_N` by caterpillar
  functions and tree face functions with `ω ≤ Δ` (`Δ ≥ 2`) uses at least
  `C(N,m)/(2Δ+2)^m` (`3 ≤ m ≤ N`), hence `(1 + 1/(2Δ+2))^N/(N+1)`, units.  Corollaries:
  `caterpillar_expansion_choose_le`, `caterpillar_expansion_exponential` (base `7/6`),
  `brunck_expansion_exponential` (the building blocks of Brunck et al., base `7/6`),
  `hingeDeg_expansion_exponential`, `outLeaf_expansion_exponential`.
* `caterpillar_expansion_quadratic`: at least `N(N-1)/6` caterpillar functions.
* `caterpillarDim_ge`: `dim(V_N/A_N) ≥ (N-2)!`.
* `bhrsy_*`, `rootedStar_ne_caterpillarFunction`: the pyramids `pyr_{e_v}(B_{v,π,M})` of
  Brunck et al. (arXiv:2610.28587v1, Sec. 7.1) are translated caterpillar polytopes for
  `M ≠ ∅` and rooted stars for `M = ∅`; rooted stars are not caterpillar functions.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar

open Corrections MaxNN.Width in
/-- **Caterpillar Net.** For every positive arity `N` there is a two-hidden-layer
ReLU network of widths `firstWidth N` and `secondWidth N` with rational weights
and zero biases computing `max_N` on all of `ℝ^N`. For `N ≥ 3`, `max_N` lies in
the span of the essential normalized caterpillar functions and the auxiliary
functions (`vocabularySpan_le_essential`); the ℚ-linear projection
(`exists_rat_coeff_of_mem_span`) makes the coefficients rational, and the
compilation theorem gives the network. -/
theorem caterpillar_net (N : ℕ) [NeZero N] :
    ∃ net : Network N (firstWidth N) (secondWidth N),
      (∀ x, net.eval x = Maximum N x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases := by
  classical
  rcases N with _ | _ | _ | r
  · exact absurd rfl (NeZero.ne 0)
  · exact caterpillar_net_one
  · exact caterpillar_net_two
  have hr : 1 ≤ r + 1 := Nat.le_add_left 1 r
  set K := essentialKeys (normalizedKeys (r + 1))
  have hKsub : K ⊆ normalizedKeys (r + 1) := essentialKeys_subset _
  let v : (↥K ⊕ Fin (W (r + 1 + 1 + 1))) → Point (r + 1 + 1 + 1) → ℝ :=
    Sum.elim (fun k => realUnitY k.1) fun j x => feat _ x j
  have hmax : MAX (r + 1 + 1 + 1) ∈ Submodule.span ℝ (Set.range v) := by
    rw [Set.Sum.elim_range, Submodule.span_union]
    exact vocabularySpan_le_essential (r + 1) (maximum_mem_dictionary (r + 1) hr)
  obtain ⟨c, hc, hcx⟩ := exists_rat_coeff_of_mem_span v
    (Sum.rec (fun k => (Canonical.realUnitY_posHomContinuous k.1
      (normalizedKeys_simplexDifference k.1 (hKsub k.2))).1)
      fun j => (Canonical.feat_posHomContinuous _ j).1)
    (Sum.rec (fun k _ hy => realUnitY_mem_ratField (ratVec_normalizedKey (hKsub k.2))
      (normalizedKeys_simplexDifference k.1 (hKsub k.2)) hy)
      fun j _ hy => feat_mem_ratField hy j)
    hmax fun y hy => MAX_mem_ratField hy
  let d : RealKey (r + 1 + 1) → ℝ := fun k => if h : k ∈ K then c (Sum.inl ⟨k, h⟩) else 0
  have hd : ∀ k (hk : k ∈ K), d k = c (Sum.inl ⟨k, hk⟩) := fun k hk => dif_pos hk
  have hle : K.card + 2 ≤ secondWidth (r + 1 + 1 + 1) := by
    have h5 := card_normalizedKeys_le_normalizedWordCones.trans
      (Nat.mul_le_mul_right (3 ^ (r + 1)) (normalized_cone_count (r + 1)))
    show K.card + 2 ≤ coneCount (r + 1 + 1 + 1) * 3 ^ (r + 1 + 1 + 1 - 2) -
      (r + 1 + 1 + 1) * (r + 1 + 1 + 1 - 1) + 2
    rw [show r + 1 + 1 + 1 - 2 = r + 1 by omega, show r + 1 + 1 + 1 - 1 = r + 1 + 1 by omega]
    exact Nat.add_le_add_right ((essentialNormalizedKeys_card_le_sub_orderedHinges hr).trans
      (Nat.sub_le_sub_right h5 _)) 2
  refine compile_expansion_width K d (fun j => c (Sum.inr j))
    (fun k hk => normalizedKeys_simplexDifference k (hKsub hk))
    (fun k hk => ratVec_normalizedKey (hKsub hk)) (fun k hk => (hd k hk).symm ▸ hc _)
    (fun j => hc _) (fun x => ?_) hle
  rw [hcx x, Fintype.sum_sum_type, ← Finset.sum_coe_sort K]
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => by rw [hd k.1 k.2]; rfl) rfl

/-- Unfold a caterpillar expansion into the internal hypotheses. -/
theorem IsCaterpillarExpansion.unfold {r : ℕ} {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) :
    K ⊆ Corrections.normalizedKeys r ∧
      ∃ (d : FaceKey r → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ),
        ∀ x, Maximum (r + 1 + 1) x =
          ∑ k in K, d k * Corrections.realUnitY k x + auxiliary a x :=
  hK

/-- **Exponential count, binomial form.** Let `N = r + 2`. If `max_N` is a linear
combination of the caterpillar functions of `K₁`, the tree face functions of `K₂` and the
auxiliary functions, and every unit of `K₂` has `ω ≤ Δ` (`Δ ≥ 2`), then
`C(N, m) ≤ (2Δ+2)^m (|K₁| + |K₂|)` for every `3 ≤ m ≤ N`. -/
theorem unified_choose_le (r : ℕ) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (Trees.TreeFace (r + 1 + 1))} (hK : Trees.IsMixedExpansion r K₁ K₂) {Δ : ℕ}
    (hΔ : 2 ≤ Δ) (hω : ∀ F ∈ K₂, Count.OmegaLe F.descr Δ) {m : ℕ} (hm : 3 ≤ m)
    (hmN : m ≤ r + 1 + 1) :
    (r + 1 + 1).choose m ≤ (2 * Δ + 2) ^ m * (K₁.card + K₂.card) :=
  Count.unified_choose_le hK hΔ hω hm hmN

/-- **Exponential count.** Under the hypotheses of `unified_choose_le`, for `N = r + 2 ≥ 3`:
`(2Δ+3)^N ≤ (N+1) (2Δ+2)^N (|K₁| + |K₂|)`. -/
theorem unified_exponential (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (Trees.TreeFace (r + 1 + 1))} (hK : Trees.IsMixedExpansion r K₁ K₂) {Δ : ℕ}
    (hΔ : 2 ≤ Δ) (hω : ∀ F ∈ K₂, Count.OmegaLe F.descr Δ) :
    (2 * Δ + 3) ^ (r + 1 + 1) ≤
      (r + 1 + 1 + 1) * (2 * Δ + 2) ^ (r + 1 + 1) * (K₁.card + K₂.card) :=
  Count.unified_exponential hr hK hΔ hω

/-- **Exponential count for caterpillars, binomial form.** Every caterpillar expansion `K`
of `max_N`, `N = r + 2`, satisfies `C(N, m) ≤ 6^m |K|` for every `3 ≤ m ≤ N`. -/
theorem caterpillar_expansion_choose_le (r : ℕ) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) {m : ℕ} (hm : 3 ≤ m) (hmN : m ≤ r + 1 + 1) :
    (r + 1 + 1).choose m ≤ 6 ^ m * K.card := by
  simpa using unified_choose_le r (Audit.isMixedExpansion_of_isCaterpillarExpansion r hK)
    le_rfl (fun F hF => absurd hF (Finset.not_mem_empty F)) hm hmN

/-- **Exponential count for caterpillars.** Every caterpillar expansion `K` of `max_N`,
`N = r + 2 ≥ 3`, satisfies `7^N ≤ (N + 1) 6^N |K|`, i.e. `|K| ≥ (7/6)^N/(N+1)`. -/
theorem caterpillar_expansion_exponential (r : ℕ) (hr : 1 ≤ r) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * K.card := by
  simpa using unified_exponential r hr (Audit.isMixedExpansion_of_isCaterpillarExpansion r hK)
    le_rfl (fun F hF => absurd hF (Finset.not_mem_empty F))

/-- **The building blocks of Brunck et al.** Every expansion of `max_N` by caterpillar
functions (`K₁`) and faces of the rooted stars (`K₂`), `N = r + 2 ≥ 3`, satisfies
`7^N ≤ (N+1) 6^N (|K₁| + |K₂|)`. -/
theorem brunck_expansion_exponential (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (Trees.TreeFace (r + 1 + 1))} (hK : Count.IsBrunckExpansion r K₁ K₂) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * (K₁.card + K₂.card) :=
  Count.brunck_unified_exponential hr hK

/-- **Bounded hinge degree.** If every tree unit of `K₂` has at most `Δ ≥ 2` hinge edges
at each vertex: `(2Δ+3)^N ≤ (N+1) (2Δ+2)^N (|K₁| + |K₂|)` for `N = r + 2 ≥ 3`. -/
theorem hingeDeg_expansion_exponential (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (Trees.TreeFace (r + 1 + 1))} (hK : Trees.IsMixedExpansion r K₁ K₂) {Δ : ℕ}
    (hΔ : 2 ≤ Δ) (hdeg : ∀ F ∈ K₂, ∀ u, F.hingeDeg u ≤ Δ) :
    (2 * Δ + 3) ^ (r + 1 + 1) ≤
      (r + 1 + 1 + 1) * (2 * Δ + 2) ^ (r + 1 + 1) * (K₁.card + K₂.card) :=
  Count.hingeDeg_unified_exponential hr hK hΔ hdeg

/-- **Few out-leaves.** If every tree unit of `K₂` has at most `s ≥ 1` out-leaves at each
vertex: `(2s+5)^N ≤ (N+1) (2s+4)^N (|K₁| + |K₂|)` for `N = r + 2 ≥ 3`. -/
theorem outLeaf_expansion_exponential (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (Trees.TreeFace (r + 1 + 1))} (hK : Trees.IsMixedExpansion r K₁ K₂) {s : ℕ}
    (hs : 1 ≤ s) (hout : ∀ F ∈ K₂, Count.OutLeafBound F.descr s) :
    (2 * s + 5) ^ (r + 1 + 1) ≤
      (r + 1 + 1 + 1) * (2 * s + 4) ^ (r + 1 + 1) * (K₁.card + K₂.card) :=
  Count.outLeaf_unified_exponential hr hK hs hout

/-- **Quadratic count.** Every caterpillar expansion `K` of `max_N`,
`N = r + 2 ≥ 3`, satisfies `N(N - 1) ≤ 6 |K|`. -/
theorem caterpillar_expansion_quadratic (r : ℕ) (hr : 1 ≤ r) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) :
    (r + 1 + 1) * (r + 1) ≤ 6 * K.card := by
  obtain ⟨hsub, d, a, h⟩ := hK.unfold
  exact caterpillar_count_lower r hr K hsub d a h

/-- The caterpillar span is the span of the dictionary. -/
theorem caterpillarSpan_eq (r : ℕ) : caterpillarSpan r = vocabularySpan r := by
  classical
  unfold caterpillarSpan vocabularySpan
  rw [dictionary_eq_range]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ (⟨k, hk, rfl⟩ | ⟨j, rfl⟩)
    · obtain ⟨k₀, hk₀, rfl⟩ := Finset.mem_image.mp hk
      apply Submodule.subset_span
      refine ⟨Sum.inl ⟨k₀, hk₀⟩, ?_⟩
      show Corrections.realUnitY k₀ = Corrections.realUnitY (Corrections.normalizedKey k₀)
      exact (Corrections.realUnitY_normalizedKey hk₀).symm
    · exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl k =>
      apply Submodule.subset_span
      refine Or.inl ⟨Corrections.normalizedKey k.1, Finset.mem_image_of_mem _ k.2, ?_⟩
      exact Corrections.realUnitY_normalizedKey k.2
    | inr j => exact Submodule.subset_span (Or.inr ⟨j, rfl⟩)

/-- `caterpillarDim` is the quotient dimension `q_N` of `Quotient.lean`. -/
theorem caterpillarDim_eq (r : ℕ) : caterpillarDim r = quotientDim r := by
  unfold caterpillarDim quotientDim
  rw [caterpillarSpan_eq]
  rfl

/-- **Dimension of the caterpillar span.** For `N = r + 2 ≥ 3`,
`dim(V_N / A_N) ≥ (N - 2)!`. -/
theorem caterpillarDim_ge (r : ℕ) (hr : 1 ≤ r) : r.factorial ≤ caterpillarDim r := by
  rw [caterpillarDim_eq]
  exact Dimension.factorial_le_quotientDim r hr

/-! ## Relation to the construction of Brunck et al.

`N = r + 2`, an apex `v`, an ordering `π` of `[N] ∖ {v}` (positions `1, …, N - 1`), and
marked positions `M ⊆ {2, …, N - 1}` as in arXiv:2610.28587v1, Sec. 7.1, Eq. (3). -/

/-- **(a) Zonotope form.** `B_{v,π,M} = e_{π_q} + ∑_{i=2}^{N-1} [0, e_{π_{r(i)}} - e_{π_i}]` with
`q = max ({1} ∪ M)` and `r(i) = max ({1} ∪ {j ∈ M : j < i})`. -/
theorem bhrsy_parallelepiped_eq_zonotope {r : ℕ} {v : Fin (r + 1 + 1)}
    (π : BHRSY.Ordering (r + 1 + 1) v) {M : Finset ℕ} (hM : M ⊆ Finset.Icc 2 (r + 1)) :
    BHRSY.parallelepiped v π M =
      zonotope (Pi.single (π.pos (BHRSY.lastMarked M)) 1) (Finset.Icc 2 (r + 1))
        (fun i => Pi.single (π.pos (BHRSY.markedParent M i)) 1 - Pi.single (π.pos i) 1) :=
  BHRSY.parallelepiped_eq_zonotope π hM

/-- **(a), `M ≠ ∅`.** `B_{v,π,M} = e_{π_{max M}} + ∑_{i=2}^{N-1} [0, e_{π_{r(i)}} - e_{π_i}]`. -/
theorem bhrsy_parallelepiped_eq_zonotope_of_nonempty {r : ℕ} {v : Fin (r + 1 + 1)}
    (π : BHRSY.Ordering (r + 1 + 1) v) {M : Finset ℕ} (hM : M ⊆ Finset.Icc 2 (r + 1))
    (hne : M.Nonempty) :
    BHRSY.parallelepiped v π M =
      zonotope (Pi.single (π.pos (M.max' hne)) 1) (Finset.Icc 2 (r + 1))
        (fun i => Pi.single (π.pos (BHRSY.markedParent M i)) 1 - Pi.single (π.pos i) 1) := by
  rw [← BHRSY.lastMarked_eq_max' hM hne]
  exact BHRSY.parallelepiped_eq_zonotope π hM

/-- **(a), `M = ∅`.** `B_{v,π,∅} = e_{π₁} + ∑_{i=2}^{N-1} [0, e_{π₁} - e_{π_i}]`. -/
theorem bhrsy_parallelepiped_empty {r : ℕ} {v : Fin (r + 1 + 1)}
    (π : BHRSY.Ordering (r + 1 + 1) v) :
    BHRSY.parallelepiped v π ∅ =
      zonotope (Pi.single (π.pos 1) 1) (Finset.Icc 2 (r + 1))
        (fun i => Pi.single (π.pos 1) 1 - Pi.single (π.pos i) 1) := by
  rw [BHRSY.parallelepiped_eq_zonotope π (Finset.empty_subset _), BHRSY.lastMarked_empty]
  simp only [BHRSY.markedParent_empty]

/-- **(b) Support function.** `h_{pyr_{e_v}(B_{v,π,M})}(y) =
y_v + σ(y_{π_q} - y_v + ∑_{i=2}^{N-1} σ(y_{π_{r(i)}} - y_{π_i}))`. -/
theorem bhrsy_support_eq {r : ℕ} {v : Fin (r + 1 + 1)} (π : BHRSY.Ordering (r + 1 + 1) v)
    {M : Finset ℕ} (hM : M ⊆ Finset.Icc 2 (r + 1)) (y : Point (r + 1 + 1)) :
    BHRSY.paramidSupport v π M y = y v + MaxCaterpillar.relu (y (π.pos (BHRSY.lastMarked M)) - y v +
      ∑ i in Finset.Icc 2 (r + 1),
        MaxCaterpillar.relu (y (π.pos (BHRSY.markedParent M i)) - y (π.pos i))) :=
  BHRSY.paramidSupport_eq π hM y

/-- **(c) The dictionary.** The support function is `y_v + U_{π',S}` for the word
`π' = (v, π₁, …, π_{N-1})` and the cut set `S = M - 1`, and `|S| = |M|`. -/
theorem bhrsy_support_eq_word {r : ℕ} {v : Fin (r + 1 + 1)} (π : BHRSY.Ordering (r + 1 + 1) v)
    {M : Finset ℕ} (hM : M ⊆ Finset.Icc 2 (r + 1)) :
    (BHRSY.cutSet (r := r) M).card = M.card ∧ ∀ y : Point (r + 1 + 1),
      BHRSY.paramidSupport v π M y =
        y v + caterpillarFunction (caterpillarWordDescription π.word (BHRSY.cutSet M)) y :=
  ⟨BHRSY.card_cutSet hM, BHRSY.paramidSupport_eq_word π hM⟩

/-- **(c) `M ≠ ∅`: caterpillar polytopes.** The support function is `y_v` plus a caterpillar
function `U_k`, `k ∈ 𝒦₀`. -/
theorem bhrsy_support_mem_caterpillar {r : ℕ} {v : Fin (r + 1 + 1)}
    (π : BHRSY.Ordering (r + 1 + 1) v) {M : Finset ℕ} (hM : M ⊆ Finset.Icc 2 (r + 1))
    (hne : M.Nonempty) :
    ∃ k ∈ caterpillarDescriptions r,
      ∀ y, BHRSY.paramidSupport v π M y = y v + caterpillarFunction k y :=
  BHRSY.exists_caterpillarDescription π hM hne

/-- **(c) Converse.** Every caterpillar word `(σ, S)` is a pyramid of Brunck et al. with
`M ≠ ∅` (namely `v = σ 0`, `π_j = σ j`, `M = S + 1`). -/
theorem bhrsy_word_mem {r : ℕ} (σ : Equiv.Perm (Fin (r + 1 + 1))) {S : Finset (Fin (r + 1))}
    (hS : S.Nonempty) (hS0 : (0 : Fin (r + 1)) ∉ S) :
    ∃ (v : Fin (r + 1 + 1)) (π : BHRSY.Ordering (r + 1 + 1) v) (M : Finset ℕ),
      M ⊆ Finset.Icc 2 (r + 1) ∧ M.Nonempty ∧ ∀ y,
        BHRSY.paramidSupport v π M y =
          y v + caterpillarFunction (caterpillarWordDescription σ S) y := by
  refine BHRSY.exists_paramid_of_word σ (Finset.mem_erase.mpr ⟨hS.ne_empty, ?_⟩)
  exact Finset.mem_powerset.mpr fun j hj =>
    Finset.mem_erase.mpr ⟨fun h => hS0 (h ▸ hj), Finset.mem_univ j⟩

/-- **(d) `M = ∅`: rooted stars.** `h_{pyr_{e_v}(B_{v,π,∅})}(y) = y_v + S_{v,π₁}(y)`. -/
theorem bhrsy_support_empty {r : ℕ} {v : Fin (r + 1 + 1)} (π : BHRSY.Ordering (r + 1 + 1) v)
    (y : Point (r + 1 + 1)) :
    BHRSY.paramidSupport v π ∅ y = y v + BHRSY.rootedStar v (π.pos 1) y :=
  BHRSY.paramidSupport_empty π y

/-- **(d) Rooted stars are not caterpillar functions** (`N = r + 2`, `a ≠ c`). -/
theorem rootedStar_ne_caterpillarFunction {r : ℕ} {a c : Fin (r + 1 + 1)} (hac : a ≠ c)
    {k : FaceKey r} (hk : k ∈ caterpillarDescriptions r) :
    BHRSY.rootedStar a c ≠ caterpillarFunction k :=
  BHRSY.rootedStar_ne_caterpillarFunction hac hk

/-- **(d)** For `M = ∅` the support function is not `y_v` plus any caterpillar function. -/
theorem bhrsy_support_empty_not_caterpillar {r : ℕ} {v : Fin (r + 1 + 1)}
    (π : BHRSY.Ordering (r + 1 + 1) v) :
    ¬ ∃ k ∈ caterpillarDescriptions r,
      ∀ y, BHRSY.paramidSupport v π ∅ y = y v + caterpillarFunction k y :=
  BHRSY.paramidSupport_empty_not_caterpillar π

/-- **The family of Brunck et al.** Every pyramid support function is `y_v` plus either a
caterpillar function (`M ≠ ∅`) or a rooted star (`M = ∅`), and not both. -/
theorem bhrsy_family {r : ℕ} {v : Fin (r + 1 + 1)} (π : BHRSY.Ordering (r + 1 + 1) v)
    {M : Finset ℕ} (hM : M ⊆ Finset.Icc 2 (r + 1)) :
    (M.Nonempty ∧ ∃ k ∈ caterpillarDescriptions r,
        ∀ y, BHRSY.paramidSupport v π M y = y v + caterpillarFunction k y) ∨
      (M = ∅ ∧ (∀ y, BHRSY.paramidSupport v π M y = y v + BHRSY.rootedStar v (π.pos 1) y) ∧
        ¬ ∃ k ∈ caterpillarDescriptions r,
          ∀ y, BHRSY.paramidSupport v π M y = y v + caterpillarFunction k y) := by
  rcases M.eq_empty_or_nonempty with h | h
  · subst h
    exact Or.inr ⟨rfl, bhrsy_support_empty π, bhrsy_support_empty_not_caterpillar π⟩
  · exact Or.inl ⟨h, bhrsy_support_mem_caterpillar π hM h⟩

end MaxCaterpillar
