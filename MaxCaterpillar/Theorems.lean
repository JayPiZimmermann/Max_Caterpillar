import MaxCaterpillar.OneBasis
import MaxCaterpillar.CountLower
import MaxCaterpillar.CountExp
import MaxCaterpillar.LowerBound
import MaxCaterpillar.Competing.Support

/-! # The public theorem interface

The objects are defined in `Definitions.lean`. The supporting development, the
Version 1 and Version 2 statements (`maximum_width`, `maximum_width_rational`,
`compilation`, …), and the internal names are in `Core.lean` and the files it
imports.

* `caterpillar_net`: the Caterpillar Net computes `max_N` with two hidden
  layers of widths `firstWidth N` and `secondWidth N`, rational weights, and
  zero biases.
* `caterpillar_expansion_choose_le`, `caterpillar_expansion_exponential`,
  `caterpillar_expansion_quadratic`: every caterpillar expansion of `max_N`
  uses at least `C(N,k)/6^k` (`3 ≤ k ≤ N`), hence `(7/6)^N/(N+1)`, and at least
  `N(N-1)/6` caterpillar functions.
* `caterpillarDim_ge`: `dim(V_N/A_N) ≥ (N-2)!`.
* `bhrsy_*`, `rootedStar_ne_caterpillarFunction`: the pyramids `pyr_{e_v}(B_{v,π,M})` of
  Brunck et al. (arXiv:2610.28587v1, Sec. 7.1; definitions in `Competing/Defs.lean`) are
  translated caterpillar polytopes for `M ≠ ∅` and rooted stars for `M = ∅`; rooted stars
  are not caterpillar functions.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar

/-- **Caterpillar Net.** For every positive arity `N` there is a two-hidden-layer
ReLU network of widths `firstWidth N` and `secondWidth N` with rational weights
and zero biases computing `max_N` on all of `ℝ^N`. (Version 3 of
`maximum_width`; the rational coefficients come from one basis of the
caterpillar span, `OneBasis.lean`.) -/
theorem caterpillar_net (N : ℕ) [NeZero N] :
    ∃ net : Network N (firstWidth N) (secondWidth N),
      (∀ x, net.eval x = Maximum N x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases :=
  maximum_width_one_basis N

/-- Unfold a caterpillar expansion into the internal hypotheses. -/
theorem IsCaterpillarExpansion.unfold {r : ℕ} {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) :
    K ⊆ Corrections.normalizedKeys r ∧
      ∃ (d : FaceKey r → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ),
        ∀ x, Maximum (r + 1 + 1) x =
          ∑ k in K, d k * Corrections.realUnitY k x + auxiliary a x :=
  hK

/-- **Exponential count, binomial form.** Every caterpillar expansion `K` of
`max_N`, `N = r + 2`, satisfies `C(N, k) ≤ 6^k |K|` for every `3 ≤ k ≤ N`. -/
theorem caterpillar_expansion_choose_le (r : ℕ) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    (r + 1 + 1).choose k ≤ 6 ^ k * K.card := by
  obtain ⟨hsub, d, a, h⟩ := hK.unfold
  exact caterpillar_count_exponential r K hsub d a h hk hkN

/-- **Exponential count.** Every caterpillar expansion `K` of `max_N`,
`N = r + 2 ≥ 3`, satisfies `7^N ≤ (N + 1) 6^N |K|`, i.e. `|K| ≥ (7/6)^N/(N+1)`. -/
theorem caterpillar_expansion_exponential (r : ℕ) (hr : 1 ≤ r) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * K.card := by
  obtain ⟨hsub, d, a, h⟩ := hK.unfold
  exact caterpillar_count_exponential_pow r hr K hsub d a h

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
  exact factorial_le_quotientDim r hr

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
    BHRSY.paramidSupport v π ∅ y = y v + Trees.rootedStar v (π.pos 1) y :=
  BHRSY.paramidSupport_empty π y

/-- **(d) Rooted stars are not caterpillar functions** (`N = r + 2`, `a ≠ c`). -/
theorem rootedStar_ne_caterpillarFunction {r : ℕ} {a c : Fin (r + 1 + 1)} (hac : a ≠ c)
    {k : FaceKey r} (hk : k ∈ caterpillarDescriptions r) :
    Trees.rootedStar a c ≠ caterpillarFunction k :=
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
      (M = ∅ ∧ (∀ y, BHRSY.paramidSupport v π M y = y v + Trees.rootedStar v (π.pos 1) y) ∧
        ¬ ∃ k ∈ caterpillarDescriptions r,
          ∀ y, BHRSY.paramidSupport v π M y = y v + caterpillarFunction k y) := by
  rcases M.eq_empty_or_nonempty with h | h
  · subst h
    exact Or.inr ⟨rfl, bhrsy_support_empty π, bhrsy_support_empty_not_caterpillar π⟩
  · exact Or.inl ⟨h, bhrsy_support_mem_caterpillar π hM h⟩

end MaxCaterpillar
