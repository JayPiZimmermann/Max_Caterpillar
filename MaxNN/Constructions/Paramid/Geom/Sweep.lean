import MaxNN.Constructions.Paramid.Geom.Sweep.Support

/-!
# The sweep operator (paper Lemma 2.1, (S1)–(S4))

Sweep data: vectors `v, w ∈ ℝ^m` with `⟨w, v⟩ = 1` (for `v ≠ 0`, `w = ⟨v, v⟩⁻¹ v` works:
`sweep_dot_normalize`).  The height of a point is `s(x) = ⟨w, x⟩`,
the projection along `v` onto the hyperplane `H = {⟨w, ·⟩ = 0}` is
`π x = sweepProj v w x = x − ⟨w, x⟩ v`, so `x = π x + s(x) v`, and its transpose is
`π* ξ = ξ − ⟨v, ξ⟩ w`.  The sweep operator (`Geom/Defs.lean`) acts on all functions:

  `(𝒯 f)(ξ) = f ξ` if `⟨v, ξ⟩ ≥ 0`, and `f (π* ξ)` otherwise.

Results (`work/depth2_simplex/CONSTRUCTIVE_SWEEP_RECONSTRUCTION_2026-10-13.md`, Lemma 2.1):

* (S1) `𝒯` is linear: `sweep_add`, `sweep_smul`, `sweep_zero`, `sweep_neg`, `sweep_sub`,
  `sweep_sum`, `sweep_fun_sum`, and the bundled linear map `sweepL`.  More generally `𝒯` is a
  precomposition (`sweep_eq_comp`) and commutes with every pointwise operation
  (`sweep_pointwise`).
* (S2) For a point set `G` of nonnegative height, `𝒯 (hS G) = hS (G ∪ π G)`, the support
  function of the prism `T(G) = conv (G ∪ π G)`: `sweep_hS_of_high` (blueprint form) and
  `sweep_hS_of_nonneg` (the same identity for arbitrary `v, w`; `⟨w, v⟩ = 1` is not needed).
  The prism has dimension at most `dim G + 1`: `finrank_vectorSpan_union_sweepProj_le`.
* (S3) `𝒯 ⟨t, ·⟩ = ⟨π t, ·⟩ + s(t) · relu ⟨v, ·⟩` (`sweep_dot`, `sweep_dot_eq`), equivalently
  `𝒯 h_{t} = h_{π t} + s(t) h_{[0, v]}` (`sweep_hS_singleton`); in particular
  `𝒯 ⟨v, ·⟩ = relu ⟨v, ·⟩ = h_{[0, v]}` (`sweep_dot_self`).
* (S4) For every nonempty `G` and every `c` with `s + c ≥ 0` on `G`:
  `𝒯 (hS G) = hS (T(G + c v)) − c · h_{[0, v]}` (`sweep_hS_eq_translate`).
* Consequences: `𝒯` maps `LSpan m k` into `LSpan m (k + 1)` (`sweep_mem_LSpan`) and `SSpan m`
  into itself (`sweep_mem_SSpan`); the cut identity is transported through `𝒯`
  (`sweep_hS_cut`).

Helpers (support functions of small sets, translates, the dimension bound, span membership) are
in `Geom/Sweep/Support.lean`, namespace `MaxNN.ParamidGeom.Sweep`.
-/

namespace MaxNN.ParamidGeom

open BigOperators

noncomputable section

variable {m : ℕ}

/-! ## Unfolding -/

theorem sweep_apply (v w : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) (ξ : Fin m → ℝ) :
    sweep v w f ξ = if 0 ≤ dot v ξ then f ξ else f (ξ - (dot v ξ) • w) := rfl

theorem sweep_of_nonneg (v w : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) {ξ : Fin m → ℝ}
    (h : 0 ≤ dot v ξ) : sweep v w f ξ = f ξ := by
  rw [sweep_apply, if_pos h]

theorem sweep_of_neg (v w : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) {ξ : Fin m → ℝ}
    (h : dot v ξ < 0) : sweep v w f ξ = f (ξ - (dot v ξ) • w) := by
  rw [sweep_apply, if_neg (not_le.mpr h)]

/-- The sweep is precomposition with the piecewise map `ξ ↦ ξ` (`⟨v, ξ⟩ ≥ 0`),
`ξ ↦ π* ξ = ξ − ⟨v, ξ⟩ w` (`⟨v, ξ⟩ < 0`). -/
theorem sweep_eq_comp (v w : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) :
    sweep v w f = fun ξ => f (if 0 ≤ dot v ξ then ξ else ξ - (dot v ξ) • w) := by
  funext ξ
  rw [sweep_apply]
  split_ifs <;> rfl

/-- Being a precomposition, the sweep commutes with every pointwise operation `Φ`. -/
theorem sweep_pointwise {ι : Type*} (v w : Fin m → ℝ) (Φ : (ι → ℝ) → ℝ)
    (F : ι → (Fin m → ℝ) → ℝ) :
    sweep v w (fun y => Φ (fun i => F i y)) = fun ξ => Φ (fun i => sweep v w (F i) ξ) := by
  simp only [sweep_eq_comp]

/-! ## (S1) Linearity -/

theorem sweep_add (v w : Fin m → ℝ) (f g : (Fin m → ℝ) → ℝ) :
    sweep v w (f + g) = sweep v w f + sweep v w g := by
  funext ξ
  simp only [sweep, Pi.add_apply]
  split_ifs <;> rfl

theorem sweep_smul (v w : Fin m → ℝ) (c : ℝ) (f : (Fin m → ℝ) → ℝ) :
    sweep v w (c • f) = c • sweep v w f := by
  funext ξ
  simp only [sweep, Pi.smul_apply]
  split_ifs <;> rfl

theorem sweep_zero (v w : Fin m → ℝ) : sweep v w 0 = 0 := by
  funext ξ
  simp only [sweep, Pi.zero_apply]
  split_ifs <;> rfl

theorem sweep_neg (v w : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) :
    sweep v w (-f) = -sweep v w f := by
  funext ξ
  simp only [sweep, Pi.neg_apply]
  split_ifs <;> rfl

theorem sweep_sub (v w : Fin m → ℝ) (f g : (Fin m → ℝ) → ℝ) :
    sweep v w (f - g) = sweep v w f - sweep v w g := by
  funext ξ
  simp only [sweep, Pi.sub_apply]
  split_ifs <;> rfl

/-- The sweep operator as an `ℝ`-linear map on functions `ℝ^m → ℝ`. -/
def sweepL (v w : Fin m → ℝ) : ((Fin m → ℝ) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) → ℝ) where
  toFun := sweep v w
  map_add' := sweep_add v w
  map_smul' c f := sweep_smul v w c f

theorem sweepL_apply (v w : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) : sweepL v w f = sweep v w f :=
  rfl

theorem sweep_sum {ι : Type*} (v w : Fin m → ℝ) (s : Finset ι) (f : ι → (Fin m → ℝ) → ℝ) :
    sweep v w (∑ i in s, f i) = ∑ i in s, sweep v w (f i) :=
  map_sum (sweepL v w) f s

/-- Linearity in pointwise form: `𝒯 (∑ aᵢ fᵢ) = ∑ aᵢ 𝒯 fᵢ`. -/
theorem sweep_fun_sum {ι : Type*} (v w : Fin m → ℝ) (s : Finset ι) (a : ι → ℝ)
    (f : ι → (Fin m → ℝ) → ℝ) :
    sweep v w (fun y => ∑ i in s, a i * f i y) = fun ξ => ∑ i in s, a i * sweep v w (f i) ξ := by
  funext ξ
  by_cases h : 0 ≤ dot v ξ
  · rw [sweep_of_nonneg v w _ h]
    exact Finset.sum_congr rfl fun i _ => by rw [sweep_of_nonneg v w _ h]
  · push_neg at h
    rw [sweep_of_neg v w _ h]
    exact Finset.sum_congr rfl fun i _ => by rw [sweep_of_neg v w _ h]

/-! ## The projection `π` and its transpose -/

/-- `⟨π x, ξ⟩ = ⟨x, ξ⟩ − s(x) ⟨v, ξ⟩`. -/
theorem dot_sweepProj (v w x ξ : Fin m → ℝ) :
    dot (sweepProj v w x) ξ = dot x ξ - dot w x * dot v ξ := by
  unfold sweepProj
  rw [SupportCut.dot_sub_left, SupportCut.dot_smul_left]

/-- `⟨x, π* ξ⟩ = ⟨π x, ξ⟩` with `π* ξ = ξ − ⟨v, ξ⟩ w`. -/
theorem dot_sub_smul_eq_dot_sweepProj (v w x ξ : Fin m → ℝ) :
    dot x (ξ - (dot v ξ) • w) = dot (sweepProj v w x) ξ := by
  rw [dot_sweepProj, SupportCut.dot_sub_right, SupportCut.dot_smul_right,
    SupportCut.dot_comm x w]
  ring

/-- Sweep data exist for every nonzero `v`: `w = ⟨v, v⟩⁻¹ v` has `⟨w, v⟩ = 1`. -/
theorem sweep_dot_normalize {v : Fin m → ℝ} (hv : v ≠ 0) : dot ((dot v v)⁻¹ • v) v = 1 := by
  rw [SupportCut.dot_smul_left]
  exact inv_mul_cancel fun h => hv (SupportCut.eq_zero_of_dot_self_eq_zero h)

/-- Every point is `π x + s(x) v`. -/
theorem sweepProj_add_smul_eq (v w x : Fin m → ℝ) : sweepProj v w x + (dot w x) • v = x := by
  unfold sweepProj
  rw [sub_add_cancel]

section SweepData

variable {v w : Fin m → ℝ}

/-- `π` lands in the hyperplane `{⟨w, ·⟩ = 0}`. -/
theorem dot_sweepProj_height (hvw : dot w v = 1) (x : Fin m → ℝ) :
    dot w (sweepProj v w x) = 0 := by
  unfold sweepProj
  rw [SupportCut.dot_sub_right, SupportCut.dot_smul_right, hvw, mul_one, sub_self]

theorem sweepProj_self (hvw : dot w v = 1) : sweepProj v w v = 0 := by
  unfold sweepProj
  rw [hvw, one_smul, sub_self]

/-- `π` is constant along `v`. -/
theorem sweepProj_add_smul (hvw : dot w v = 1) (x : Fin m → ℝ) (c : ℝ) :
    sweepProj v w (x + c • v) = sweepProj v w x := by
  unfold sweepProj
  rw [SupportCut.dot_add_right, SupportCut.dot_smul_right, hvw, mul_one, add_smul]
  abel

/-- `⟨v, π* ξ⟩ = 0`. -/
theorem sweep_dual_dot_eq_zero (hvw : dot w v = 1) (ξ : Fin m → ℝ) :
    dot v (ξ - (dot v ξ) • w) = 0 := by
  rw [SupportCut.dot_sub_right, SupportCut.dot_smul_right, SupportCut.dot_comm v w, hvw,
    mul_one, sub_self]

end SweepData

/-! ## (S2) The sweep of a high point set is the support function of its prism -/

/-- **(S2)**, for arbitrary `v, w`: if `⟨w, ·⟩ ≥ 0` on `G`, then
`𝒯 (hS G) = hS (G ∪ π G)`.  For `⟨v, ξ⟩ ≥ 0` every `⟨π p, ξ⟩ ≤ ⟨p, ξ⟩`; for `⟨v, ξ⟩ < 0` the
inequality reverses and `max_p ⟨π p, ξ⟩ = max_p ⟨p, π* ξ⟩ = hS G (π* ξ)`. -/
theorem sweep_hS_of_nonneg (v w : Fin m → ℝ) (G : Finset (Fin m → ℝ))
    (hG : ∀ p ∈ G, 0 ≤ dot w p) :
    sweep v w (hS G) = hS (G ∪ G.image (sweepProj v w)) := by
  funext ξ
  rcases G.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.image_empty, Finset.empty_union]
    simp only [sweep, Sweep.hS_empty, ite_self]
  · have hne' : (G ∪ G.image (sweepProj v w)).Nonempty := hne.mono (Finset.subset_union_left _ _)
    rw [hS_of_nonempty hne']
    by_cases h : 0 ≤ dot v ξ
    · rw [sweep_of_nonneg v w _ h, hS_of_nonempty hne]
      apply le_antisymm
      · exact Finset.sup'_mono _ (Finset.subset_union_left _ _) hne
      · refine Finset.sup'_le _ _ fun q hq => ?_
        rcases Finset.mem_union.mp hq with hq | hq
        · exact Finset.le_sup' (fun p => dot p ξ) hq
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
          have h1 : dot (sweepProj v w p) ξ ≤ dot p ξ := by
            rw [dot_sweepProj]
            have := mul_nonneg (hG p hp) h
            linarith
          exact le_trans h1 (Finset.le_sup' (fun p => dot p ξ) hp)
    · push_neg at h
      rw [sweep_of_neg v w _ h, hS_of_nonempty hne]
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun p hp => ?_
        rw [dot_sub_smul_eq_dot_sweepProj]
        exact Finset.le_sup' (fun p => dot p ξ)
          (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
      · refine Finset.sup'_le _ _ fun q hq => ?_
        rcases Finset.mem_union.mp hq with hq | hq
        · have h1 : dot q ξ ≤ dot q (ξ - (dot v ξ) • w) := by
            rw [dot_sub_smul_eq_dot_sweepProj, dot_sweepProj]
            have := mul_nonneg (hG q hq) (neg_nonneg.mpr h.le)
            linarith
          exact le_trans h1 (Finset.le_sup' (fun p => dot p (ξ - (dot v ξ) • w)) hq)
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
          rw [← dot_sub_smul_eq_dot_sweepProj]
          exact Finset.le_sup' (fun p => dot p (ξ - (dot v ξ) • w)) hp

/-- The prism `G ∪ π G` has affine dimension at most `dim aff G + 1` (any `v, w`). -/
theorem finrank_vectorSpan_union_image_sweepProj_le (v w : Fin m → ℝ)
    (G : Finset (Fin m → ℝ)) :
    FiniteDimensional.finrank ℝ
        (vectorSpan ℝ (↑(G ∪ G.image (sweepProj v w)) : Set (Fin m → ℝ))) ≤
      FiniteDimensional.finrank ℝ (vectorSpan ℝ (G : Set (Fin m → ℝ))) + 1 := by
  apply Sweep.finrank_vectorSpan_le_add_one_of_forall v
  intro x hx
  rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx | hx
  · exact ⟨x, Finset.mem_coe.mpr hx, 0, by rw [zero_smul, add_zero]⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨p, Finset.mem_coe.mpr hp, -dot w p, ?_⟩
    show p - dot w p • v = p + (-dot w p) • v
    rw [neg_smul, sub_eq_add_neg]

/-! ## (S3) The sweep of a linear form -/

/-- **(S3)**, for arbitrary `v, w`: `𝒯 ⟨t, ·⟩ = ⟨π t, ·⟩ + s(t) · relu ⟨v, ·⟩`. -/
theorem sweep_dot_eq (v w t : Fin m → ℝ) :
    sweep v w (dot t) = fun ξ => dot (sweepProj v w t) ξ + dot w t * relu (dot v ξ) := by
  funext ξ
  show sweep v w (dot t) ξ = dot (sweepProj v w t) ξ + dot w t * relu (dot v ξ)
  rw [dot_sweepProj]
  by_cases h : 0 ≤ dot v ξ
  · rw [sweep_of_nonneg v w _ h, relu_of_nonneg h]
    ring
  · push_neg at h
    rw [sweep_of_neg v w _ h, relu_of_nonpos h.le, SupportCut.dot_sub_right,
      SupportCut.dot_smul_right, SupportCut.dot_comm t w]
    ring

/-- **(S3)** for support functions: `𝒯 h_{t} = h_{π t} + s(t) h_{[0, v]}`. -/
theorem sweep_hS_singleton (v w t : Fin m → ℝ) :
    sweep v w (hS {t}) = hS {sweepProj v w t} + dot w t • hS {0, v} := by
  rw [Sweep.hS_singleton, Sweep.hS_singleton, sweep_dot_eq]
  funext ξ
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sweep.hS_pair_zero]

section SweepData

variable {v w : Fin m → ℝ}

set_option linter.unusedVariables false in
/-- **(S2)** (blueprint form): if `⟨w, v⟩ = 1` and `G` is high (`⟨w, ·⟩ ≥ 0` on `G`), then
`𝒯 (hS G) = hS (G ∪ π G)`.  The normalization `hvw` is part of the sweep data and fixes `v`;
the identity itself holds without it (`sweep_hS_of_nonneg`). -/
theorem sweep_hS_of_high (hvw : dot w v = 1) (G : Finset (Fin m → ℝ))
    (hG : ∀ p ∈ G, 0 ≤ dot w p) :
    sweep v w (hS G) = hS (G ∪ G.image (sweepProj v w)) :=
  sweep_hS_of_nonneg v w G hG

set_option linter.unusedVariables false in
/-- The prism `G ∪ π G` has affine dimension at most `dim aff G + 1` (blueprint form; the bound
holds for all `v, w`, `finrank_vectorSpan_union_image_sweepProj_le`). -/
theorem finrank_vectorSpan_union_sweepProj_le (hvw : dot w v = 1) (G : Finset (Fin m → ℝ)) :
    FiniteDimensional.finrank ℝ
        (vectorSpan ℝ (↑(G ∪ G.image (sweepProj v w)) : Set (Fin m → ℝ))) ≤
      FiniteDimensional.finrank ℝ (vectorSpan ℝ (G : Set (Fin m → ℝ))) + 1 :=
  finrank_vectorSpan_union_image_sweepProj_le v w G

set_option linter.unusedVariables false in
/-- **(S3)** in closed form (blueprint form): `𝒯 ⟨t, ·⟩ = ⟨π t, ·⟩ + ⟨w, t⟩ · relu ⟨v, ·⟩`.
The identity holds for all `v, w` (`sweep_dot_eq`). -/
theorem sweep_dot (hvw : dot w v = 1) (t : Fin m → ℝ) :
    sweep v w (dot t) = fun ξ => dot (sweepProj v w t) ξ + dot w t * relu (dot v ξ) :=
  sweep_dot_eq v w t

/-- **(S3)**, special case: `𝒯 ⟨v, ·⟩ = relu ⟨v, ·⟩ = h_{[0, v]}`. -/
theorem sweep_dot_self (hvw : dot w v = 1) : sweep v w (dot v) = fun ξ => relu (dot v ξ) := by
  rw [sweep_dot_eq, sweepProj_self hvw, hvw]
  funext ξ
  rw [Sweep.dot_zero_left, zero_add, one_mul]

/-! ## (S4) Sweeping an arbitrary point set -/

/-- **(S4)**: for a nonempty point set `G` and `c` with `s + c ≥ 0` on `G`, the translate
`G + c v` is high and `𝒯 (hS G) = hS (T(G + c v)) − c · h_{[0, v]}`. -/
theorem sweep_hS_eq_translate (hvw : dot w v = 1) {G : Finset (Fin m → ℝ)} (hne : G.Nonempty)
    (c : ℝ) (hc : ∀ p ∈ G, 0 ≤ dot w p + c) :
    sweep v w (hS G) =
      hS (G.image (fun p => p + c • v) ∪ (G.image (fun p => p + c • v)).image (sweepProj v w)) -
        c • hS {0, v} := by
  have hhigh : ∀ q ∈ G.image (fun p => p + c • v), 0 ≤ dot w q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [SupportCut.dot_add_right, SupportCut.dot_smul_right, hvw, mul_one]
    exact hc p hp
  rw [← sweep_hS_of_nonneg v w _ hhigh]
  funext ξ
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Sweep.hS_pair_zero]
  by_cases h : 0 ≤ dot v ξ
  · rw [sweep_of_nonneg v w _ h, sweep_of_nonneg v w _ h, Sweep.hS_image_add_smul hne,
      relu_of_nonneg h]
    ring
  · push_neg at h
    rw [sweep_of_neg v w _ h, sweep_of_neg v w _ h, Sweep.hS_image_add_smul hne,
      relu_of_nonpos h.le, sweep_dual_dot_eq_zero hvw]
    ring

/-- The sweep of the support function of a nonempty set `S` is a prism support function minus a
multiple of the segment `h_{[0, v]}`, the prism having dimension at most `dim aff S + 1`. -/
theorem sweep_hS_eq_prism_sub (hvw : dot w v = 1) {S : Finset (Fin m → ℝ)} (hne : S.Nonempty) :
    ∃ (P : Finset (Fin m → ℝ)) (c : ℝ), P.Nonempty ∧
      FiniteDimensional.finrank ℝ (vectorSpan ℝ (P : Set (Fin m → ℝ))) ≤
        FiniteDimensional.finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) + 1 ∧
      sweep v w (hS S) = hS P - c • hS {0, v} := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ p ∈ S, 0 ≤ dot w p + c := by
    refine ⟨S.sup' hne (fun p => -dot w p), fun p hp => ?_⟩
    have h : -dot w p ≤ S.sup' hne (fun p => -dot w p) := Finset.le_sup' (fun p => -dot w p) hp
    linarith
  refine ⟨S.image (fun p => p + c • v) ∪ (S.image (fun p => p + c • v)).image (sweepProj v w), c,
    (hne.image _).mono (Finset.subset_union_left _ _), ?_, sweep_hS_eq_translate hvw hne c hc⟩
  apply Sweep.finrank_vectorSpan_le_add_one_of_forall v
  intro x hx
  rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx | hx
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨p, Finset.mem_coe.mpr hp, c, rfl⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨p, Finset.mem_coe.mpr hp, c - dot w (p + c • v), ?_⟩
    show p + c • v - dot w (p + c • v) • v = p + (c - dot w (p + c • v)) • v
    rw [sub_smul]
    abel

/-! ## The sweep raises the dimension by at most one -/

/-- The sweep of the support function of a nonempty set of affine dimension `≤ k` lies in
`LSpan m (k + 1)`. -/
theorem sweep_hS_mem_LSpan (hvw : dot w v = 1) {k : ℕ} {S : Finset (Fin m → ℝ)}
    (hne : S.Nonempty)
    (hdim : FiniteDimensional.finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) ≤ k) :
    sweep v w (hS S) ∈ LSpan m (k + 1) := by
  obtain ⟨P, c, hPne, hPdim, he⟩ := sweep_hS_eq_prism_sub hvw hne
  rw [he]
  exact sub_mem (Sweep.hS_mem_LSpan hPne (le_trans hPdim (Nat.add_le_add_right hdim 1)))
    (Submodule.smul_mem _ c (Sweep.hS_mem_LSpan (Finset.insert_nonempty _ _)
      (le_trans (Sweep.finrank_vectorSpan_pair_zero_le v) (Nat.le_add_left 1 k))))

/-- **The sweep raises the dimension by at most one:** `𝒯 (LSpan m k) ⊆ LSpan m (k + 1)`. -/
theorem sweep_mem_LSpan (hvw : dot w v = 1) {k : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hf : f ∈ LSpan m k) : sweep v w f ∈ LSpan m (k + 1) := by
  have key : LSpan m k ≤ (LSpan m (k + 1)).comap (sweepL v w) := by
    refine Submodule.span_le.mpr ?_
    intro g hg
    obtain ⟨S, hne, hdim, rfl⟩ := Sweep.eq_hS_of_mem_lowerDimSupport hg
    rw [SetLike.mem_coe, Submodule.mem_comap, sweepL_apply]
    exact sweep_hS_mem_LSpan hvw hne hdim
  have h := key hf
  rwa [Submodule.mem_comap, sweepL_apply] at h

/-- The sweep maps `SSpan m` into itself. -/
theorem sweep_mem_SSpan (hvw : dot w v = 1) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) :
    sweep v w f ∈ SSpan m := by
  have key : SSpan m ≤ (SSpan m).comap (sweepL v w) := by
    refine Submodule.span_le.mpr ?_
    rintro g ⟨S, hne, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, sweepL_apply]
    obtain ⟨P, c, hPne, -, he⟩ := sweep_hS_eq_prism_sub hvw hne
    rw [he]
    exact sub_mem (Sweep.hS_mem_SSpan hPne)
      (Submodule.smul_mem _ c (Sweep.hS_mem_SSpan (Finset.insert_nonempty _ _)))
  have h := key hf
  rwa [Submodule.mem_comap, sweepL_apply] at h

end SweepData

/-! ## (S7) The cut identity transported through the sweep -/

/-- The cut identity of `PolyhedralGeometry/SupportCut.lean` survives the sweep (linearity):
`𝒯 h_S + 𝒯 h_{S⁰ ∪ M} = 𝒯 h_{S⁺ ∪ M} + 𝒯 h_{S⁻ ∪ M}`. -/
theorem sweep_hS_cut (v w : Fin m → ℝ) (S : Finset (Fin m → ℝ)) (a : Fin m → ℝ) (c : ℝ)
    (h0 : (SupportCut.sectionPoints S a c).Nonempty) :
    sweep v w (hS S) + sweep v w (hS (SupportCut.sectionPoints S a c)) =
      sweep v w (hS (SupportCut.upperPoints S a c)) +
        sweep v w (hS (SupportCut.lowerPoints S a c)) := by
  rw [← sweep_add, ← sweep_add, Sweep.hS_cut_identity S a c h0]

end

end MaxNN.ParamidGeom
