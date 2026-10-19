import MaxNN.Constructions.Paramid.Geom.Reconstruct.SimplexCut.CutSets

/-!
# Local facts about the sweep operator (helper for `Geom/Reconstruct/SimplexCut.lean`)

`Geom/Sweep.lean` (the wave-0 module of the blueprint) did not exist when this file was written,
so the few sweep facts needed by the simplex reconstruction are proved here, in the sub-namespace
`MaxNN.ParamidGeom.SimplexCut` (so that they cannot clash with the names of `Geom/Sweep.lean`):

* `sweep_hS_of_high`: for a point set `G` with `⟨w, g⟩ ≥ 0` on `G`,
  `sweep v w (hS G) = hS (G ∪ G.image (sweepProj v w))` (no hypothesis on `⟨w, v⟩` is needed);
* `sweep_add_eq_of_add_eq`: the sweep transports pointwise identities `f₁ + f₂ = f₃ + f₄`;
* `finrank_vectorSpan_prism_le`: the prism `G ∪ π G` has affine dimension `≤ dim G + 1`;
* `sweep_hS_mem_LSpan_of_high`: hence `sweep v w (hS G) ∈ LSpan m (k + 1)` for a high `G` of
  dimension `≤ k`.
-/

namespace MaxNN.ParamidGeom

namespace SimplexCut

open BigOperators MaxNN.SupportCut

noncomputable section

variable {m : ℕ}

theorem dot_sweepProj_left (v w g ξ : Fin m → ℝ) :
    dot (sweepProj v w g) ξ = dot g ξ - dot w g * dot v ξ := by
  rw [sweepProj, dot_sub_left, dot_smul_left]

theorem dot_sub_dot_smul_right (v w g ξ : Fin m → ℝ) :
    dot g (ξ - dot v ξ • w) = dot g ξ - dot w g * dot v ξ := by
  rw [dot_sub_right, dot_smul_right, dot_comm g w, mul_comm]

/-- `h_{π G}(ξ) = h_G(ξ − ⟨v, ξ⟩ w)` for the projection `π = sweepProj v w`. -/
theorem hS_image_sweepProj (v w : Fin m → ℝ) (G : Finset (Fin m → ℝ)) (ξ : Fin m → ℝ) :
    hS (G.image (sweepProj v w)) ξ = hS G (ξ - dot v ξ • w) := by
  by_cases hne : G.Nonempty
  · rw [hS_of_nonempty (hne.image _), hS_of_nonempty hne, Finset.sup'_image]
    congr 1
    funext g
    simp only [Function.comp_apply, dot_sweepProj_left, dot_sub_dot_smul_right]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp [hS]

/-- **The sweep of a high point set is the support function of its prism.** -/
theorem sweep_hS_of_high (v w : Fin m → ℝ) (G : Finset (Fin m → ℝ))
    (hG : ∀ g ∈ G, 0 ≤ dot w g) :
    sweep v w (hS G) = hS (G ∪ G.image (sweepProj v w)) := by
  funext ξ
  by_cases hne : G.Nonempty
  · have hmax : hS (G ∪ G.image (sweepProj v w)) ξ =
        max (hS G ξ) (hS (G.image (sweepProj v w)) ξ) := by
      rw [hS_of_nonempty (hne.mono (Finset.subset_union_left _ _)), hS_of_nonempty hne,
        hS_of_nonempty (hne.image _)]
      exact Finset.sup'_union hne (hne.image _) _
    rw [hmax, hS_image_sweepProj]
    unfold sweep
    split_ifs with h
    · refine (max_eq_left ?_).symm
      rw [hS_of_nonempty hne, hS_of_nonempty hne]
      refine Finset.sup'_le _ _ fun g hg => le_trans ?_ (Finset.le_sup' (fun p => dot p ξ) hg)
      rw [dot_sub_dot_smul_right]
      nlinarith [hG g hg]
    · refine (max_eq_right ?_).symm
      rw [hS_of_nonempty hne, hS_of_nonempty hne]
      refine Finset.sup'_le _ _ fun g hg =>
        le_trans ?_ (Finset.le_sup' (fun p => dot p (ξ - dot v ξ • w)) hg)
      rw [dot_sub_dot_smul_right]
      push_neg at h
      nlinarith [hG g hg]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp [sweep, hS]

/-- The sweep transports pointwise identities `f₁ + f₂ = f₃ + f₄`. -/
theorem sweep_add_eq_of_add_eq {f₁ f₂ f₃ f₄ : (Fin m → ℝ) → ℝ}
    (h : ∀ y, f₁ y + f₂ y = f₃ y + f₄ y) (v w y : Fin m → ℝ) :
    sweep v w f₁ y + sweep v w f₂ y = sweep v w f₃ y + sweep v w f₄ y := by
  unfold sweep
  split_ifs
  · exact h y
  · exact h _

/-- The prism `G ∪ π G` lies in `aff G + ℝ v`, so its dimension is at most `dim G + 1`. -/
theorem finrank_vectorSpan_prism_le (v w : Fin m → ℝ) (G : Finset (Fin m → ℝ)) :
    FiniteDimensional.finrank ℝ
        (vectorSpan ℝ (↑(G ∪ G.image (sweepProj v w)) : Set (Fin m → ℝ))) ≤
      FiniteDimensional.finrank ℝ (vectorSpan ℝ (↑G : Set (Fin m → ℝ))) + 1 := by
  have hform : ∀ x ∈ (↑(G ∪ G.image (sweepProj v w)) : Set (Fin m → ℝ)),
      ∃ g ∈ G, ∃ α : ℝ, x = g + α • v := by
    intro x hx
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx | hx
    · exact ⟨x, hx, 0, by rw [zero_smul, add_zero]⟩
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨g, hg, -dot w g, by rw [sweepProj, neg_smul, sub_eq_add_neg]⟩
  have hle : vectorSpan ℝ (↑(G ∪ G.image (sweepProj v w)) : Set (Fin m → ℝ)) ≤
      vectorSpan ℝ (↑G : Set (Fin m → ℝ)) ⊔ Submodule.span ℝ {v} := by
    rw [vectorSpan_def, Submodule.span_le]
    intro z hz
    obtain ⟨x, y, hx, hy, rfl⟩ := Set.mem_vsub.mp hz
    obtain ⟨g, hg, α, rfl⟩ := hform x hx
    obtain ⟨g', hg', β, rfl⟩ := hform y hy
    have e : (g + α • v) -ᵥ (g' + β • v) = (g -ᵥ g') + (α - β) • v := by
      rw [vsub_eq_sub, vsub_eq_sub, sub_smul]
      abel
    rw [SetLike.mem_coe, e]
    exact Submodule.add_mem_sup
      (vsub_mem_vectorSpan ℝ (Finset.mem_coe.mpr hg) (Finset.mem_coe.mpr hg'))
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  have hv1 : FiniteDimensional.finrank ℝ (Submodule.span ℝ ({v} : Set (Fin m → ℝ))) ≤ 1 := by
    have h := finrank_span_le_card (K := ℝ) ({v} : Set (Fin m → ℝ))
    simpa using h
  calc FiniteDimensional.finrank ℝ
        (vectorSpan ℝ (↑(G ∪ G.image (sweepProj v w)) : Set (Fin m → ℝ)))
      ≤ FiniteDimensional.finrank ℝ
          ↥(vectorSpan ℝ (↑G : Set (Fin m → ℝ)) ⊔ Submodule.span ℝ {v}) :=
        Submodule.finrank_mono hle
    _ ≤ FiniteDimensional.finrank ℝ (vectorSpan ℝ (↑G : Set (Fin m → ℝ))) +
          FiniteDimensional.finrank ℝ (Submodule.span ℝ ({v} : Set (Fin m → ℝ))) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ FiniteDimensional.finrank ℝ (vectorSpan ℝ (↑G : Set (Fin m → ℝ))) + 1 :=
        Nat.add_le_add_left hv1 _

/-- The sweep of a high point set of dimension `≤ k` lies in `LSpan m (k + 1)`. -/
theorem sweep_hS_mem_LSpan_of_high (v w : Fin m → ℝ) {G : Finset (Fin m → ℝ)}
    (hG : ∀ g ∈ G, 0 ≤ dot w g) {k : ℕ}
    (hdim : FiniteDimensional.finrank ℝ (vectorSpan ℝ (↑G : Set (Fin m → ℝ))) ≤ k) :
    sweep v w (hS G) ∈ LSpan m (k + 1) := by
  rw [sweep_hS_of_high v w G hG]
  exact hS_mem_LSpan_of_finrank_le
    ((finrank_vectorSpan_prism_le v w G).trans (Nat.add_le_add_right hdim 1))

end

end SimplexCut

end MaxNN.ParamidGeom
