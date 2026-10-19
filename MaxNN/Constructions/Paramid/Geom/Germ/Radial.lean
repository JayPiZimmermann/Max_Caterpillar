import MaxNN.Constructions.Paramid.Geom.Germ

/-! # Radial translation of a directional germ

For any function in the support-function span, the germ at `u` is affine along
`u`, with slope `f u`. This all-dimensional identity is the first step of the
reflection branch for braid-facet cancellation.
-/

namespace MaxNN.ParamidGeom

open GermAux

variable {m : ℕ}

theorem hS_add_smul_of_constant_dot {S : Finset (Fin m → ℝ)} (hSne : S.Nonempty)
    (u : Fin m → ℝ) (c : ℝ) (hc : ∀ p ∈ S, dot p u = c) (y : Fin m → ℝ) (t : ℝ) :
    hS S (y + t • u) = hS S y + t * c := by
  apply le_antisymm
  · obtain ⟨p, hp, he⟩ := exists_mem_hS_eq hSne (y + t • u)
    rw [he, SupportCut.dot_add_right, SupportCut.dot_smul_right, hc p hp]
    exact add_le_add_right (dot_le_hS hp y) _
  · obtain ⟨p, hp, he⟩ := exists_mem_hS_eq hSne y
    rw [he]
    have h := dot_le_hS hp (y + t • u)
    rwa [SupportCut.dot_add_right, SupportCut.dot_smul_right, hc p hp] at h

theorem germ_add_smul_direction {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m)
    (u y : Fin m → ℝ) (t : ℝ) : germ f u (y + t • u) = germ f u y + t * f u := by
  have h : f ∈ SSpan m ∧ ∀ (u y : Fin m → ℝ) (t : ℝ),
      germ f u (y + t • u) = germ f u y + t * f u := by
    refine Submodule.span_induction (p := fun f => f ∈ SSpan m ∧
      ∀ (u y : Fin m → ℝ) (t : ℝ), germ f u (y + t • u) = germ f u y + t * f u)
      hf ?_ ?_ ?_ ?_
    · rintro _ ⟨S, hSne, rfl⟩
      refine ⟨hS_mem_SSpan hSne, fun u y t => ?_⟩
      rw [germ_hS hSne]
      exact hS_add_smul_of_constant_dot (face_nonempty hSne u) u (hS S u)
        (fun p hp => (hS_eq_dot_of_mem_face hp).symm) y t
    · refine ⟨Submodule.zero_mem _, fun u y t => ?_⟩
      rw [germ_zero]
      simp only [Pi.zero_apply, mul_zero, add_zero]
    · rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
      refine ⟨Submodule.add_mem _ hf hg, fun u y t => ?_⟩
      rw [germ_add hf hg]
      simp only [Pi.add_apply, hf', hg']
      ring
    · rintro a f ⟨hf, hf'⟩
      refine ⟨Submodule.smul_mem _ a hf, fun u y t => ?_⟩
      rw [germ_smul a hf]
      simp only [Pi.smul_apply, smul_eq_mul, hf']
      ring
  exact h.2 u y t

theorem IsGerm.comp_linearMap {f df : (Fin m → ℝ) → ℝ}
    (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (u : Fin m → ℝ)
    (h : IsGerm f (L u) df) :
    IsGerm (fun y => f (L y)) u (fun y => df (L y)) := by
  intro y
  simpa only [map_add, map_smul] using h (L y)

end MaxNN.ParamidGeom
