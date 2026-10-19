import MaxNN.Constructions.Paramid.Geom.Defs
import MaxNN.PolyhedralGeometry.SupportCut

/-!
# Support functions, translates and a dimension bound (helpers for `Geom/Sweep.lean`)

Elementary facts about the support function `hS` of `Geom/Defs.lean` that the sweep operator
needs, and nothing else:

* `hS ∅ = 0`, `hS {t} = ⟨t, ·⟩`, `hS {0, v} = relu ⟨v, ·⟩` (the segment `[0, v]`);
* translation (R_T): `hS (G + c v) = hS G + c ⟨v, ·⟩` for nonempty `G`
  (`hS_image_add_smul`, written with `G.image (· + c • v)`);
* (R_H): `hS` depends only on the convex hull (`hS_eq_of_convexHull_eq`), with the one-sided
  form `hS_le_of_subset_convexHull`;
* the cut identity of `PolyhedralGeometry/SupportCut.lean` at the level of `hS`
  (`hS_cut_identity`);
* a dimension bound: if every point of `T` is `s + a • v` with `s ∈ S`, then the affine span of
  `T` has dimension at most `dim aff S + 1` (`finrank_vectorSpan_le_add_one_of_forall`);
* membership of `hS T` in `LSpan m k` and `SSpan m`, and monotonicity of `LSpan m k` in `k`.

Everything lives in the namespace `MaxNN.ParamidGeom.Sweep`, so that these generic names cannot
collide with lemmas of the other `Geom` modules.
-/

namespace MaxNN.ParamidGeom

namespace Sweep

open BigOperators

variable {m : ℕ}

/-! ## Small support functions -/

theorem dot_zero_left (ξ : Fin m → ℝ) : dot (0 : Fin m → ℝ) ξ = 0 := by
  show ∑ i, (0 : Fin m → ℝ) i * ξ i = 0
  exact Finset.sum_eq_zero fun i _ => zero_mul (ξ i)

theorem hS_empty (y : Fin m → ℝ) : hS (∅ : Finset (Fin m → ℝ)) y = 0 := by
  unfold hS
  rw [dif_neg Finset.not_nonempty_empty]

/-- The support function of a single point is the linear form of that point. -/
theorem hS_singleton (t : Fin m → ℝ) : hS ({t} : Finset (Fin m → ℝ)) = dot t := by
  funext y
  rw [hS_of_nonempty (Finset.singleton_nonempty t), Finset.sup'_singleton]

/-- The support function of the segment `[0, v]` is the hinge `relu ⟨v, ·⟩`. -/
theorem hS_pair_zero (v ξ : Fin m → ℝ) :
    hS ({0, v} : Finset (Fin m → ℝ)) ξ = relu (dot v ξ) := by
  rw [hS_of_nonempty (Finset.insert_nonempty 0 {v})]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun p hp => ?_
    rcases Finset.mem_insert.mp hp with rfl | hp
    · show dot 0 ξ ≤ relu (dot v ξ)
      rw [dot_zero_left]
      exact relu_nonneg _
    · rw [Finset.mem_singleton.mp hp]
      exact le_max_right 0 (dot v ξ)
  · show max 0 (dot v ξ) ≤ _
    refine max_le ?_ ?_
    · have h : dot (0 : Fin m → ℝ) ξ ≤ _ :=
        Finset.le_sup' (fun p => dot p ξ) (Finset.mem_insert_self (0 : Fin m → ℝ) {v})
      rw [dot_zero_left] at h
      exact h
    · exact Finset.le_sup' (fun p => dot p ξ)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))

/-! ## Translation (R_T) -/

theorem sup'_add_const {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (a : ℝ) :
    s.sup' hs (fun i => f i + a) = s.sup' hs f + a := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i hi => add_le_add_right (Finset.le_sup' f hi) a
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hs f
    rw [he]
    exact Finset.le_sup' (fun i => f i + a) hi

/-- **(R_T)** Translating a nonempty point set by `c • v` adds `c ⟨v, ·⟩` to its support
function. -/
theorem hS_image_add_smul {G : Finset (Fin m → ℝ)} (hG : G.Nonempty) (c : ℝ)
    (v ξ : Fin m → ℝ) :
    hS (G.image (fun p => p + c • v)) ξ = hS G ξ + c * dot v ξ := by
  rw [hS_of_nonempty (hG.image _), hS_of_nonempty hG, Finset.sup'_image,
    ← sup'_add_const G hG (fun p => dot p ξ) (c * dot v ξ)]
  have e : ((fun p => dot p ξ) ∘ fun p => p + c • v) = fun p => dot p ξ + c * dot v ξ := by
    funext p
    show dot (p + c • v) ξ = dot p ξ + c * dot v ξ
    rw [SupportCut.dot_add_left, SupportCut.dot_smul_left]
  rw [e]

/-! ## (R_H) `hS` depends only on the convex hull -/

/-- A linear form is bounded on `conv S` by its maximum over `S`. -/
theorem dot_le_hS_of_mem_convexHull {S : Finset (Fin m → ℝ)} {x : Fin m → ℝ}
    (hx : x ∈ convexHull ℝ (S : Set (Fin m → ℝ))) (y : Fin m → ℝ) : dot x y ≤ hS S y := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.coe_empty, convexHull_empty] at hx
    exact absurd hx (Set.not_mem_empty x)
  rw [hS_of_nonempty hne]
  have hconv : Convex ℝ {z : Fin m → ℝ | dot y z ≤ S.sup' hne (fun p => dot p y)} :=
    convex_halfspace_le (SupportCut.dotL y).isLinear _
  have hsub : (S : Set (Fin m → ℝ)) ⊆ {z | dot y z ≤ S.sup' hne (fun p => dot p y)} := by
    intro p hp
    show dot y p ≤ _
    rw [SupportCut.dot_comm]
    exact Finset.le_sup' (fun p => dot p y) (Finset.mem_coe.mp hp)
  have h := convexHull_min hsub hconv hx
  show dot x y ≤ _
  rw [SupportCut.dot_comm]
  exact h

/-- If `S' ⊆ conv S` then `hS S' ≤ hS S`. -/
theorem hS_le_of_subset_convexHull {S S' : Finset (Fin m → ℝ)} (hne' : S'.Nonempty)
    (h : (S' : Set (Fin m → ℝ)) ⊆ convexHull ℝ (S : Set (Fin m → ℝ))) (y : Fin m → ℝ) :
    hS S' y ≤ hS S y := by
  rw [hS_of_nonempty hne']
  exact Finset.sup'_le _ _ fun p hp => dot_le_hS_of_mem_convexHull (h (Finset.mem_coe.mpr hp)) y

/-- **(R_H)** Point sets with the same convex hull have the same support function. -/
theorem hS_eq_of_convexHull_eq {S S' : Finset (Fin m → ℝ)}
    (h : convexHull ℝ (S : Set (Fin m → ℝ)) = convexHull ℝ (S' : Set (Fin m → ℝ))) :
    hS S = hS S' := by
  have hiff : S.Nonempty ↔ S'.Nonempty := by
    rw [← Finset.coe_nonempty, ← Finset.coe_nonempty, ← convexHull_nonempty_iff (𝕜 := ℝ), h,
      convexHull_nonempty_iff]
  funext y
  rcases S.eq_empty_or_nonempty with hS0 | hne
  · have hS'0 : S' = ∅ := by
      rcases S'.eq_empty_or_nonempty with h' | h'
      · exact h'
      · exact absurd (hiff.mpr h') (by rw [hS0]; exact Finset.not_nonempty_empty)
    rw [hS0, hS'0]
  · apply le_antisymm
    · exact hS_le_of_subset_convexHull hne ((subset_convexHull ℝ _).trans h.subset) y
    · exact hS_le_of_subset_convexHull (hiff.mp hne) ((subset_convexHull ℝ _).trans h.symm.subset) y

/-! ## The cut identity at the level of `hS` -/

/-- `PolyhedralGeometry/SupportCut.lean`, Theorem B, for the support function `hS`:
`hS S + hS (S⁰ ∪ M) = hS (S⁺ ∪ M) + hS (S⁻ ∪ M)` whenever the section `S⁰ ∪ M` is nonempty. -/
theorem hS_cut_identity (S : Finset (Fin m → ℝ)) (a : Fin m → ℝ) (c : ℝ)
    (h0 : (SupportCut.sectionPoints S a c).Nonempty) :
    hS S + hS (SupportCut.sectionPoints S a c) =
      hS (SupportCut.upperPoints S a c) + hS (SupportCut.lowerPoints S a c) := by
  funext y
  show hS S y + hS (SupportCut.sectionPoints S a c) y =
    hS (SupportCut.upperPoints S a c) y + hS (SupportCut.lowerPoints S a c) y
  rw [hS_of_nonempty (SupportCut.nonempty_of_nonempty_sectionPoints h0), hS_of_nonempty h0,
    hS_of_nonempty (SupportCut.nonempty_upperPoints h0),
    hS_of_nonempty (SupportCut.nonempty_lowerPoints h0)]
  exact SupportCut.support_cut_identity S a c h0 y

/-! ## A dimension bound for sets swept along a line -/

/-- If every point of `T` is `s + a • v` with `s ∈ S`, then `vectorSpan T ≤ vectorSpan S + ℝ v`. -/
theorem vectorSpan_le_sup_span_of_forall {S T : Set (Fin m → ℝ)} (v : Fin m → ℝ)
    (h : ∀ x ∈ T, ∃ s ∈ S, ∃ a : ℝ, x = s + a • v) :
    vectorSpan ℝ T ≤ vectorSpan ℝ S ⊔ Submodule.span ℝ {v} := by
  rw [vectorSpan_def, Submodule.span_le]
  intro z hz
  obtain ⟨x, y, hx, hy, rfl⟩ := Set.mem_vsub.mp hz
  obtain ⟨s, hs, a, rfl⟩ := h x hx
  obtain ⟨s', hs', a', rfl⟩ := h y hy
  have e : (s + a • v) -ᵥ (s' + a' • v) = (s -ᵥ s') + (a - a') • v := by
    rw [vsub_eq_sub, vsub_eq_sub, sub_smul]
    abel
  rw [SetLike.mem_coe, e]
  exact Submodule.add_mem_sup (vsub_mem_vectorSpan ℝ hs hs')
    (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))

/-- If every point of `T` is `s + a • v` with `s ∈ S`, then
`dim aff T ≤ dim aff S + 1`. -/
theorem finrank_vectorSpan_le_add_one_of_forall {S T : Set (Fin m → ℝ)} (v : Fin m → ℝ)
    (h : ∀ x ∈ T, ∃ s ∈ S, ∃ a : ℝ, x = s + a • v) :
    FiniteDimensional.finrank ℝ (vectorSpan ℝ T) ≤
      FiniteDimensional.finrank ℝ (vectorSpan ℝ S) + 1 := by
  have h1 : FiniteDimensional.finrank ℝ (Submodule.span ℝ ({v} : Set (Fin m → ℝ))) ≤ 1 := by
    have h2 := finrank_span_finset_le_card (K := ℝ) ({v} : Finset (Fin m → ℝ))
    rw [Finset.coe_singleton, Finset.card_singleton] at h2
    exact h2
  calc FiniteDimensional.finrank ℝ (vectorSpan ℝ T)
      ≤ FiniteDimensional.finrank ℝ ↥(vectorSpan ℝ S ⊔ Submodule.span ℝ {v}) :=
        Submodule.finrank_mono (vectorSpan_le_sup_span_of_forall v h)
    _ ≤ FiniteDimensional.finrank ℝ (vectorSpan ℝ S) +
          FiniteDimensional.finrank ℝ (Submodule.span ℝ ({v} : Set (Fin m → ℝ))) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ FiniteDimensional.finrank ℝ (vectorSpan ℝ S) + 1 := Nat.add_le_add_left h1 _

/-- The segment `{0, v}` has affine dimension at most `1`. -/
theorem finrank_vectorSpan_pair_zero_le (v : Fin m → ℝ) :
    FiniteDimensional.finrank ℝ
      (vectorSpan ℝ ((({0, v} : Finset (Fin m → ℝ))) : Set (Fin m → ℝ))) ≤ 1 := by
  have h := finrank_vectorSpan_le_add_one_of_forall (S := ({0} : Set (Fin m → ℝ)))
    (T := ((({0, v} : Finset (Fin m → ℝ))) : Set (Fin m → ℝ))) v ?_
  · rw [vectorSpan_singleton, finrank_bot, zero_add] at h
    exact h
  · intro x hx
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hx
    · exact ⟨0, Set.mem_singleton 0, 0, by rw [zero_smul, add_zero]⟩
    · rw [Finset.mem_singleton.mp hx]
      exact ⟨0, Set.mem_singleton 0, 1, by rw [one_smul, zero_add]⟩

/-! ## Membership in the spans -/

/-- A support function of a nonempty set of affine dimension `≤ k` lies in `LSpan m k`. -/
theorem hS_mem_LSpan {k : ℕ} {T : Finset (Fin m → ℝ)} (hT : T.Nonempty)
    (hdim : FiniteDimensional.finrank ℝ (vectorSpan ℝ (T : Set (Fin m → ℝ))) ≤ k) :
    hS T ∈ LSpan m k := by
  apply Submodule.subset_span
  exact ⟨T, hT, hdim, fun y => hS_of_nonempty hT y⟩

theorem hS_mem_SSpan {T : Finset (Fin m → ℝ)} (hT : T.Nonempty) : hS T ∈ SSpan m := by
  apply Submodule.subset_span
  exact ⟨T, hT, rfl⟩

theorem LSpan_mono {k k' : ℕ} (h : k ≤ k') : LSpan m k ≤ LSpan m k' := by
  apply Submodule.span_mono
  rintro f ⟨S, hne, hdim, hf⟩
  exact ⟨S, hne, le_trans hdim h, hf⟩

/-- Every generator of `LSpan m k` is the support function `hS S` of a nonempty set `S` of affine
dimension `≤ k`. -/
theorem eq_hS_of_mem_lowerDimSupport {k : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hf : f ∈ LowerDimSupport m k) :
    ∃ S : Finset (Fin m → ℝ), S.Nonempty ∧
      FiniteDimensional.finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) ≤ k ∧ f = hS S := by
  obtain ⟨S, hne, hdim, hfS⟩ := hf
  exact ⟨S, hne, hdim, funext fun y => (hfS y).trans (hS_of_nonempty hne y).symm⟩

end Sweep

end MaxNN.ParamidGeom
