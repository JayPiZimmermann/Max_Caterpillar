import MaxNN.Constructions.Paramid.Geom.Induction.SimplexFacet

/-! # Facet data of the standard simplex away from coordinate rays

The full-dimensional facet directions of the standard simplex are precisely
the rays spanned by its outer normals.  Away from those rays, both exposed
faces have affine dimension at most two below the ambient dimension.  This
module records the resulting direct `LSpan` statement needed by the
caterpillar completeness argument.
-/

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {r : ℕ}

/-- Exact facet datum in an outer-normal direction.  The non-linear summand
is the support function of the opposite facet, expressed as an affine image
of the next smaller standard simplex; the remaining two summands are linear. -/
theorem germDiff_hS_simplexVerts_nu (a : Fin (r + 1 + 1)) :
    germDiff (ParamidGeom.nu a) (hS (simplexVerts (r + 1))) = fun y =>
      hS (simplexVerts r) ((Matrix.transpose (ParamidGeom.faceMat a)).mulVec y) +
        dot (toR (vtx (a.succAbove 0))) y - dot (toR (vtx a)) y := by
  funext y
  rw [germDiff_hS (SimplexFacetAux.simplexVerts_nonempty (r + 1)),
    SimplexFacetAux.face_nu, SimplexFacetAux.face_neg_nu,
    SimplexFacetAux.image_succAbove_eq]
  change hS ((simplexVerts r).image (fun p =>
      (ParamidGeom.faceMat a).mulVec p + toR (vtx (a.succAbove 0)))) y -
      hS ({toR (vtx a)} : Finset (Fin (r + 1) → ℝ)) y = _
  rw [
    SimplexFacetAux.hS_image_affine _ _ (SimplexFacetAux.simplexVerts_nonempty r),
    GermAux.hS_singleton]

/-- The support function of the standard basis is the coordinate maximum. -/
theorem hS_standardBasis_eq_MAX (n : ℕ) :
    hS (Finset.univ.image (fun i : Fin (n + 1) =>
      (Pi.single i 1 : Fin (n + 1) → ℝ))) = MAX (n + 1) := by
  funext y
  let B : Finset (Fin (n + 1) → ℝ) := Finset.univ.image fun i => Pi.single i 1
  have hB : B.Nonempty := Finset.univ_nonempty.image _
  change hS B y = MAX (n + 1) y
  rw [hS_of_nonempty hB]
  apply le_antisymm
  · apply Finset.sup'_le
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    rw [SupportCut.dot_comm, SimplexFacetAux.dot_single_one]
    exact le_MAX (n + 1) y i
  · obtain ⟨i, hi⟩ := exists_MAX_eq (n + 1) y
    rw [hi]
    have hle := Finset.le_sup' (fun p => dot p y)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩ : Pi.single i 1 ∈ B)
    rwa [SupportCut.dot_comm, SimplexFacetAux.dot_single_one] at hle

/-- In the canonical all-ones direction, the positive face consists of all
standard basis vertices and the negative face is the origin.  Its facet datum
is therefore exactly the coordinate maximum in the same ambient space. -/
theorem germDiff_hS_simplexVerts_one (n : ℕ) :
    germDiff (fun _ : Fin (n + 1) => (1 : ℝ))
      (hS (simplexVerts (n + 1))) = MAX (n + 1) := by
  have hone : (fun _ : Fin (n + 1) => (1 : ℝ)) =
      ParamidGeom.nu (0 : Fin (n + 1 + 1)) := ParamidGeom.nu_zero.symm
  rw [hone, germDiff_hS (SimplexFacetAux.simplexVerts_nonempty (n + 1)),
    SimplexFacetAux.face_nu, SimplexFacetAux.face_neg_nu, GermAux.hS_singleton]
  have himage : Finset.univ.image
      (fun b : Fin (n + 1) => toR (vtx ((0 : Fin (n + 1 + 1)).succAbove b))) =
      Finset.univ.image (fun b : Fin (n + 1) => (Pi.single b 1 : Fin (n + 1) → ℝ)) := by
    apply Finset.image_congr
    intro b _
    change toR (vtx ((0 : Fin (n + 1 + 1)).succAbove b)) = Pi.single b 1
    rw [Fin.zero_succAbove, SimplexFacetAux.toR_vtx_succ]
  rw [himage, hS_standardBasis_eq_MAX]
  have hzero : dot (toR (vtx (0 : Fin (n + 1 + 1)))) =
      (0 : (Fin (n + 1) → ℝ) → ℝ) := by
    funext y
    rw [SimplexFacetAux.toR_vtx_zero, SupportCut.dot_comm,
      SimplexFacetAux.dot_zero_right]
    rfl
  rw [hzero]
  funext y
  simp

/-- Away from every outer-normal ray, the two-sided germ of the standard
simplex belongs to the span two dimensions below the ambient dimension. -/
theorem germDiff_hS_simplexVerts_mem_LSpan_of_forall_ne_smul_nu
    (hr : 2 ≤ r) (u : Fin (r + 1) → ℝ)
    (hu : ∀ (a : Fin (r + 1 + 1)) (c : ℝ), u ≠ c • ParamidGeom.nu a) :
    germDiff u (hS (simplexVerts (r + 1))) ∈ LSpan (r + 1) (r - 1) := by
  have hne := SimplexFacetAux.simplexVerts_nonempty (r + 1)
  have hneg : ∀ (a : Fin (r + 1 + 1)) (c : ℝ), -u ≠ c • ParamidGeom.nu a := by
    intro a c h
    apply hu a (-c)
    rw [neg_smul, ← h, neg_neg]
  rw [germDiff_hS hne]
  apply Submodule.sub_mem
  · apply FlagAux.hS_mem_LSpan (face_nonempty hne u)
    apply SimplexFacetAux.finrank_vectorSpan_le_of_card_le (face_nonempty hne u)
    have hc := SimplexFacetAux.card_face_le u hu
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using hc
  · apply FlagAux.hS_mem_LSpan (face_nonempty hne (-u))
    apply SimplexFacetAux.finrank_vectorSpan_le_of_card_le (face_nonempty hne (-u))
    have hc := SimplexFacetAux.card_face_le (-u) hneg
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using hc

end MaxNN.Caterpillar
