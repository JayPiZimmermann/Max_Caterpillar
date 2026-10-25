import MaxNN.Constructions.Paramid.Geom.Faces.Defs
import MaxNN.Constructions.Paramid.Geom.Faces.Peel.Pieces

/-!
# Eliminate a lower-dimensional expression one direction space at a time

For a face-closed family, a function in its span and in `LSpan m d`, with
`d < dim U`, is already in the relative face span. Apply `I - germ(·, u)`
once for each polytope in a lower-dimensional expression, choosing `u`
orthogonal to that polytope but not to `U`. Earlier operations produce
only support functions of its subsets, which the chosen operation also
annihilates. This avoids simultaneous generic directions and induction
on dimension. The finite-sup induction below is the same finite product
without introducing an operator or assuming that germs commute.
-/

namespace MaxNN.ParamidGeom.Faces

open BigOperators FiniteDimensional PeelAux

variable {m : ℕ}

private def subsetSpan (S : Finset (Fin m → ℝ)) :
    Submodule ℝ ((Fin m → ℝ) → ℝ) := FSpan {F | F ⊆ S}

private theorem subsets_faceClosed (S : Finset (Fin m → ℝ)) :
    FaceClosed {F | F ⊆ S} :=
  fun F hF u => (face_subset u F).trans hF

private theorem germ_eq_self_on_subsetSpan {S : Finset (Fin m → ℝ)}
    {u : Fin m → ℝ} (hu : u ∈ ann (vectorSpan ℝ (S : Set (Fin m → ℝ))))
    {g : (Fin m → ℝ) → ℝ} (hg : g ∈ subsetSpan S) : germ g u = g := by
  apply germ_eq_of_isGerm
  refine Submodule.span_induction (p := fun f => IsGerm f u f) hg ?_ ?_ ?_ ?_
  · rintro _ ⟨F, hF, hne, rfl⟩
    have hface : face u F = F := face_eq_self_of_orth fun p hp q hq =>
      mem_ann.mp hu (p - q) (by
        rw [← vsub_eq_sub]
        exact vsub_mem_vectorSpan ℝ (hF hp) (hF hq))
    simpa only [hface] using isGerm_hS hne u
  · exact isGerm_zero u
  · exact fun _ _ h₁ h₂ => h₁.add h₂
  · exact fun c _ h => h.smul c

private theorem sup_subsetSpan_le_SSpan (P : Finset (Finset (Fin m → ℝ))) :
    P.sup subsetSpan ≤ SSpan m :=
  Finset.sup_le fun _ _ => FSpan_le_SSpan _

private theorem germ_mem_sup_subsetSpan (P : Finset (Finset (Fin m → ℝ)))
    {g : (Fin m → ℝ) → ℝ} (hg : g ∈ P.sup subsetSpan) (u : Fin m → ℝ) :
    germ g u ∈ P.sup subsetSpan := by
  classical
  induction P using Finset.induction_on generalizing g with
  | empty =>
    simp only [Finset.sup_empty, Submodule.mem_bot] at hg ⊢
    rw [hg, germ_zero]
  | @insert S P _ ih =>
    rw [Finset.sup_insert] at hg ⊢
    obtain ⟨f, hf, q, hq, rfl⟩ := Submodule.mem_sup.mp hg
    rw [germ_add (FSpan_le_SSpan _ hf) (sup_subsetSpan_le_SSpan P hq)]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (germ_mem_FSpan (subsets_faceClosed S) hf u))
      (Submodule.mem_sup_right (ih hq))

private theorem mem_relative_of_mem_sup_subsetSpan
    {𝔉 : Set (Finset (Fin m → ℝ))} (U : Submodule ℝ (Fin m → ℝ))
    (h𝔉 : FaceClosed 𝔉) (P : Finset (Finset (Fin m → ℝ)))
    (hP : ∀ S ∈ P, finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) < finrank ℝ U)
    {g : (Fin m → ℝ) → ℝ} (hgF : g ∈ FSpan 𝔉) (hgP : g ∈ P.sup subsetSpan) :
    g ∈ GSpanRel 𝔉 U := by
  classical
  induction P using Finset.induction_on generalizing g with
  | empty =>
    have hg0 : g = 0 := by simpa using hgP
    rw [hg0]
    exact Submodule.zero_mem _
  | @insert S P _ ih =>
    obtain ⟨w, hwU, hwS⟩ : ∃ w ∈ U, w ∉ vectorSpan ℝ (S : Set (Fin m → ℝ)) := by
      by_contra h
      push_neg at h
      exact (not_le_of_gt (hP S (Finset.mem_insert_self _ _)))
        (Submodule.finrank_mono fun w hw => h w hw)
    obtain ⟨u, huS, huw⟩ := exists_mem_ann_dot_ne_zero hwS
    have huU : ∃ w ∈ U, dot u w ≠ 0 := ⟨w, hwU, huw⟩
    have hcutF : g - germ g u ∈ FSpan 𝔉 :=
      Submodule.sub_mem _ hgF (germ_mem_FSpan h𝔉 hgF u)
    have hcutP : g - germ g u ∈ P.sup subsetSpan := by
      rw [Finset.sup_insert] at hgP
      obtain ⟨f, hf, q, hq, rfl⟩ := Submodule.mem_sup.mp hgP
      rw [germ_add (FSpan_le_SSpan _ hf) (sup_subsetSpan_le_SSpan P hq),
        germ_eq_self_on_subsetSpan huS hf,
        show f + q - (f + germ q u) = q - germ q u by abel]
      exact Submodule.sub_mem _ hq (germ_mem_sup_subsetSpan P hq u)
    have hcut := ih (fun S hS => hP S (Finset.mem_insert_of_mem hS)) hcutF hcutP
    simpa only [sub_add_cancel] using
      Submodule.add_mem (GSpanRel 𝔉 U) hcut (germ_mem_GSpanRel U hgF huU)

/-- **Relative face elimination.** A lower-dimensional expression in a face-closed
family is a combination of its faces in directions that do not annihilate `U`.
No additional linear remainder or simultaneous generic directions are needed. -/
theorem mem_GSpanRel_of_lt_finrank (U : Submodule ℝ (Fin m → ℝ))
    {𝔉 : Set (Finset (Fin m → ℝ))} (h𝔉 : FaceClosed 𝔉)
    {d : ℕ} (hd : d < finrank ℝ U) {g : (Fin m → ℝ) → ℝ}
    (hgF : g ∈ FSpan 𝔉) (hgL : g ∈ LSpan m d) : g ∈ GSpanRel 𝔉 U := by
  classical
  obtain ⟨r, b, S, hne, hdim, heq⟩ := exists_hS_decomp hgL
  let P := Finset.univ.image S
  refine mem_relative_of_mem_sup_subsetSpan U h𝔉 P ?_ hgF ?_
  · intro F hF
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hF
    exact (hdim i).trans_lt hd
  · rw [heq]
    have hs : (fun y => ∑ i, b i * hS (S i) y) = ∑ i, b i • hS (S i) := by
      ext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hs]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact (Finset.le_sup (f := subsetSpan) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
      (hS_mem_FSpan (Finset.Subset.refl _) (hne i))

end MaxNN.ParamidGeom.Faces
