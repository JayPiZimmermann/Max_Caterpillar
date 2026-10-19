import MaxNN.Constructions.Paramid.Caterpillar.Formula.Facets
import MaxNN.Constructions.Paramid.Caterpillar.Block.Levels
import MaxNN.Constructions.Paramid.Geom.Complete.Chart
import MaxNN.Constructions.Paramid.Geom.Induction.SimplexFacet

/-! # Coordinate directions among two-level simplex directions -/

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {r : ℕ}

/-- The reduced direction induced by the full vertex value which is one at
`a` and zero at every other simplex vertex. -/
def coordinateDirection (a : Fin (r + 1 + 1)) : Fin (r + 1) → ℝ :=
  fun i => (if i.succ = a then 1 else 0) - (if (0 : Fin (r + 1 + 1)) = a then 1 else 0)

theorem simplexValues_coordinateDirection (a b : Fin (r + 1 + 1)) :
    simplexValues (coordinateDirection a) b =
      (if b = a then 1 else 0) - (if (0 : Fin (r + 1 + 1)) = a then 1 else 0) := by
  refine Fin.cases ?_ (fun i => ?_) b
  · rw [simplexValues_zero, sub_self]
  · rw [simplexValues_succ]
    rfl

theorem eq_smul_coordinateDirection_of_singleton_level
    (u : Fin (r + 1) → ℝ) (a : Fin (r + 1 + 1)) (c : ℝ)
    (hother : ∀ b, b ≠ a → simplexValues u b = c) :
    u = (simplexValues u a - c) • coordinateDirection a := by
  have hx : ∀ b, simplexValues u b =
      c + (simplexValues u a - c) * (if b = a then 1 else 0) := by
    intro b
    by_cases hba : b = a
    · subst b
      rw [if_pos rfl]
      ring
    · rw [if_neg hba, hother b hba]
      ring
  have hzero := hx 0
  rw [simplexValues_zero] at hzero
  funext i
  have hi := hx i.succ
  rw [simplexValues_succ] at hi
  change u i = (simplexValues u a - c) *
    ((if i.succ = a then 1 else 0) - (if (0 : Fin (r + 1 + 1)) = a then 1 else 0))
  nlinarith only [hi, hzero]

/-- A two-level full simplex direction either has no singleton level, or is
a scalar multiple of a reduced coordinate direction. -/
theorem repeatedValues_or_smul_coordinateDirection (u : Fin (r + 1) → ℝ)
    (hblock : BlockDirection u) :
    RepeatedValues (simplexValues u) ∨
      ∃ a : Fin (r + 1 + 1), ∃ t : ℝ, u = t • coordinateDirection a := by
  classical
  by_cases hrep : RepeatedValues (simplexValues u)
  · exact Or.inl hrep
  · right
    obtain ⟨a, ha⟩ : ∃ a, ∀ b, b ≠ a →
        simplexValues u b ≠ simplexValues u a := by
      simpa only [RepeatedValues, not_forall, not_exists, not_and] using hrep
    obtain ⟨c, d, hcd⟩ := hblock
    rcases hcd a with hac | had
    · refine ⟨a, simplexValues u a - d,
        eq_smul_coordinateDirection_of_singleton_level u a d ?_⟩
      intro b hba
      rcases hcd b with hbc | hbd
      · exact False.elim (ha b hba (hbc.trans hac.symm))
      · exact hbd
    · refine ⟨a, simplexValues u a - c,
        eq_smul_coordinateDirection_of_singleton_level u a c ?_⟩
      intro b hba
      rcases hcd b with hbc | hbd
      · exact hbc
      · exact False.elim (ha b hba (hbd.trans had.symm))

theorem permutedInput_swap_zero_one (a : Fin (r + 1 + 1)) :
    permutedInput (Equiv.swap 0 a) (fun _ : Fin (r + 1) => (1 : ℝ)) =
      -coordinateDirection a := by
  funext i
  unfold permutedInput coordinateDirection
  by_cases ha0 : a = 0
  · subst a
    simp only [Equiv.swap_self, Equiv.refl_apply, simplexValues_succ, simplexValues_zero,
      if_pos rfl, if_neg (Fin.succ_ne_zero i), Pi.neg_apply, ite_true]
    ring
  · obtain ⟨k, rfl⟩ := (Fin.eq_zero_or_eq_succ a).resolve_left ha0
    by_cases hik : i = k
    · subst i
      simp only [Pi.neg_apply]
      rw [Equiv.swap_apply_right, Equiv.swap_apply_left, simplexValues_zero,
        simplexValues_succ]
      rw [if_neg (Fin.succ_ne_zero k).symm]
      norm_num
    · have hia : i.succ ≠ k.succ := fun he => hik (Fin.succ_injective _ he)
      simp only [Pi.neg_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i) hia,
        Equiv.swap_apply_left, simplexValues_succ, simplexValues_succ,
        if_neg hia, if_neg (Fin.succ_ne_zero k).symm]
      ring

theorem permutedInput_comp (σ τ : Equiv.Perm (Fin (r + 1 + 1)))
    (y : Fin (r + 1) → ℝ) :
    permutedInput σ (permutedInput τ y) = permutedInput (σ.trans τ) y := by
  funext i
  change simplexValues (permutedInput τ y) (σ i.succ) -
      simplexValues (permutedInput τ y) (σ 0) =
    simplexValues y ((σ.trans τ) i.succ) - simplexValues y ((σ.trans τ) 0)
  rw [simplexValues_permutedInput, simplexValues_permutedInput]
  simp only [Equiv.trans_apply]
  ring

theorem permutedInput_refl (y : Fin (r + 1) → ℝ) :
    permutedInput (Equiv.refl _) y = y := by
  funext i
  unfold permutedInput
  rw [Equiv.refl_apply, Equiv.refl_apply, simplexValues_succ, simplexValues_zero, sub_zero]

noncomputable def permutedInputLinearEquiv (τ : Equiv.Perm (Fin (r + 1 + 1))) :
    (Fin (r + 1) → ℝ) ≃ₗ[ℝ] (Fin (r + 1) → ℝ) where
  toFun := permutedInput τ
  invFun := permutedInput τ.symm
  left_inv y := by
    change permutedInput τ.symm (permutedInput τ y) = y
    rw [permutedInput_comp, Equiv.symm_trans_self, permutedInput_refl]
  right_inv y := by
    change permutedInput τ (permutedInput τ.symm y) = y
    rw [permutedInput_comp, Equiv.self_trans_symm, permutedInput_refl]
  map_add' y z := by
    funext i
    unfold permutedInput simplexValues
    simp only [SupportCut.dot_add_right, Pi.add_apply]
    ring
  map_smul' c y := by
    funext i
    unfold permutedInput simplexValues
    simp only [SupportCut.dot_smul_right, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem permutedInputLinearEquiv_apply (τ : Equiv.Perm (Fin (r + 1 + 1)))
    (y : Fin (r + 1) → ℝ) : permutedInputLinearEquiv τ y = permutedInput τ y := rfl

noncomputable def linearMapMatrix
    (L : (Fin (r + 1) → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ)) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin (r + 1))) (Pi.basisFun ℝ (Fin (r + 1))) L

theorem linearMapMatrix_mulVec
    (L : (Fin (r + 1) → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ))
    (y : Fin (r + 1) → ℝ) : (linearMapMatrix L).mulVec y = L y := by
  simpa only [linearMapMatrix, Pi.basisFun_repr] using
    L.toMatrix_mulVec_repr (Pi.basisFun ℝ (Fin (r + 1)))
      (Pi.basisFun ℝ (Fin (r + 1))) y

theorem comp_linearMap_mem_LSpan
    (L : (Fin (r + 1) → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ))
    {k : ℕ} {f : (Fin (r + 1) → ℝ) → ℝ} (hf : f ∈ LSpan (r + 1) k) :
    (fun y => f (L y)) ∈ LSpan (r + 1) k := by
  have h := CompleteAux.comp_mulVec_mem_LSpan' (linearMapMatrix L) hf
  simpa only [linearMapMatrix_mulVec] using h

theorem comp_linearEquiv_mem_LSpan_iff
    (L : (Fin (r + 1) → ℝ) ≃ₗ[ℝ] (Fin (r + 1) → ℝ))
    {k : ℕ} {f : (Fin (r + 1) → ℝ) → ℝ} :
    (fun y => f (L y)) ∈ LSpan (r + 1) k ↔ f ∈ LSpan (r + 1) k := by
  constructor
  · intro h
    have hi := comp_linearMap_mem_LSpan L.symm.toLinearMap h
    change (fun y => f (L (L.symm y))) ∈ LSpan (r + 1) k at hi
    simpa only [L.apply_symm_apply] using hi
  · exact comp_linearMap_mem_LSpan L.toLinearMap

/-- Formula facet data are equivariant under a simplex-vertex permutation.
The translation error in `formula_permutedInput` is linear and hence drops
out of `germDiff`. -/
theorem germDiff_formula_permutedInputLinearEquiv
    (τ : Equiv.Perm (Fin (r + 1 + 1))) (u : Fin (r + 1) → ℝ) :
    (fun y => germDiff (permutedInputLinearEquiv τ u) (formula r)
      (permutedInputLinearEquiv τ y)) = germDiff u (formula r) := by
  let L := (permutedInputLinearEquiv τ).toLinearMap
  let p := (-totalWeight r) • toR (vtx (τ 0))
  have hcomp : germDiff u (fun y => formula r (L y)) =
      fun y => germDiff (L u) (formula r) (L y) := by
    funext y
    rw [germDiff_eq_sub, germDiff_eq_sub]
    rw [germ_eq_of_isGerm
        ((isGerm_germ_of_mem_SSpan (formula_mem_SSpan r) (L u)).comp_linearMap L u),
      germ_eq_of_isGerm
        ((isGerm_germ_of_mem_SSpan (formula_mem_SSpan r) (L (-u))).comp_linearMap L (-u))]
    rw [map_neg]
    rfl
  have hformula : (fun y => formula r (L y)) = formula r + dot p := by
    funext y
    change formula r (permutedInput τ y) = formula r y + dot p y
    rw [formula_permutedInput, SupportCut.dot_smul_left]
    change formula r y - totalWeight r * simplexValues y (τ 0) =
      formula r y + (-totalWeight r) * simplexValues y (τ 0)
    ring
  change (fun y => germDiff (L u) (formula r) (L y)) = germDiff u (formula r)
  rw [← hcomp, hformula, germDiff_add (formula_mem_SSpan r) (GermAux.dot_mem_SSpan p),
    germDiff_dot, add_zero]

theorem germDiff_formula_coordinate_transport (a : Fin (r + 1 + 1)) :
    (fun y => germDiff (-coordinateDirection a) (formula r)
      (permutedInputLinearEquiv (Equiv.swap 0 a) y)) =
      germDiff (fun _ : Fin (r + 1) => (1 : ℝ)) (formula r) := by
  have h := germDiff_formula_permutedInputLinearEquiv (r := r) (Equiv.swap 0 a)
    (fun _ : Fin (r + 1) => (1 : ℝ))
  rwa [permutedInputLinearEquiv_apply, permutedInput_swap_zero_one] at h

theorem toR_vtx_mem_simplexVerts (a : Fin (r + 1 + 1)) :
    toR (vtx a) ∈ simplexVerts (r + 1) := by
  rw [SimplexFacetAux.simplexVerts_eq_image]
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

/-- Permuting the vertices in reduced simplex coordinates changes the simplex
support function only by the common translation of all vertex values. -/
theorem hS_simplexVerts_permutedInput (τ : Equiv.Perm (Fin (r + 1 + 1)))
    (y : Fin (r + 1) → ℝ) :
    hS (simplexVerts (r + 1)) (permutedInput τ y) =
      hS (simplexVerts (r + 1)) y - simplexValues y (τ 0) := by
  apply le_antisymm
  · rw [hS_of_nonempty (SimplexFacetAux.simplexVerts_nonempty (r + 1))]
    refine Finset.sup'_le _ _ fun p hp => ?_
    rw [SimplexFacetAux.simplexVerts_eq_image] at hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    change simplexValues (permutedInput τ y) a ≤
      hS (simplexVerts (r + 1)) y - simplexValues y (τ 0)
    rw [simplexValues_permutedInput]
    exact sub_le_sub_right
      (GermAux.dot_le_hS (toR_vtx_mem_simplexVerts (τ a)) y) _
  · obtain ⟨p, hp, hpy⟩ := GermAux.exists_mem_hS_eq
      (SimplexFacetAux.simplexVerts_nonempty (r + 1)) y
    rw [SimplexFacetAux.simplexVerts_eq_image] at hp
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hp
    have hle := GermAux.dot_le_hS
      (toR_vtx_mem_simplexVerts (τ.symm b)) (permutedInput τ y)
    change simplexValues (permutedInput τ y) (τ.symm b) ≤
      hS (simplexVerts (r + 1)) (permutedInput τ y) at hle
    rw [simplexValues_permutedInput, τ.apply_symm_apply] at hle
    change hS (simplexVerts (r + 1)) y = simplexValues y b at hpy
    linarith

/-- The residual between the caterpillar formula and the standard simplex
support function. Its facet data are the quantities controlled in the final
lower-dimensional comparison. -/
noncomputable def coordinateResidual (r : ℕ) : (Fin (r + 1) → ℝ) → ℝ :=
  formula r - hS (simplexVerts (r + 1))

theorem coordinateResidual_mem_SSpan (r : ℕ) : coordinateResidual r ∈ SSpan (r + 1) := by
  exact Submodule.sub_mem _ (formula_mem_SSpan r)
    (GermAux.hS_mem_SSpan (SimplexFacetAux.simplexVerts_nonempty (r + 1)))

theorem coordinateResidual_permutedInput (τ : Equiv.Perm (Fin (r + 1 + 1)))
    (y : Fin (r + 1) → ℝ) :
    coordinateResidual r (permutedInput τ y) = coordinateResidual r y +
      (1 - totalWeight r) * simplexValues y (τ 0) := by
  unfold coordinateResidual
  change formula r (permutedInput τ y) -
      hS (simplexVerts (r + 1)) (permutedInput τ y) =
    formula r y - hS (simplexVerts (r + 1)) y +
      (1 - totalWeight r) * simplexValues y (τ 0)
  rw [formula_permutedInput, hS_simplexVerts_permutedInput]
  ring

/-- Facet data of the residual are equivariant under every simplex-vertex
permutation. The remaining error from the affine recentering is linear. -/
theorem germDiff_coordinateResidual_permutedInputLinearEquiv
    (τ : Equiv.Perm (Fin (r + 1 + 1))) (u : Fin (r + 1) → ℝ) :
    (fun y => germDiff (permutedInputLinearEquiv τ u) (coordinateResidual r)
      (permutedInputLinearEquiv τ y)) = germDiff u (coordinateResidual r) := by
  let L := (permutedInputLinearEquiv τ).toLinearMap
  let p := (1 - totalWeight r) • toR (vtx (τ 0))
  have hcomp : germDiff u (fun y => coordinateResidual r (L y)) =
      fun y => germDiff (L u) (coordinateResidual r) (L y) := by
    funext y
    rw [germDiff_eq_sub, germDiff_eq_sub]
    rw [germ_eq_of_isGerm
        ((isGerm_germ_of_mem_SSpan (coordinateResidual_mem_SSpan r) (L u)).comp_linearMap L u),
      germ_eq_of_isGerm
        ((isGerm_germ_of_mem_SSpan (coordinateResidual_mem_SSpan r) (L (-u))).comp_linearMap L (-u))]
    rw [map_neg]
    rfl
  have hresidual : (fun y => coordinateResidual r (L y)) =
      coordinateResidual r + dot p := by
    funext y
    change coordinateResidual r (permutedInput τ y) = coordinateResidual r y + dot p y
    rw [coordinateResidual_permutedInput, SupportCut.dot_smul_left]
    rfl
  change (fun y => germDiff (L u) (coordinateResidual r) (L y)) =
    germDiff u (coordinateResidual r)
  rw [← hcomp, hresidual,
    germDiff_add (coordinateResidual_mem_SSpan r) (GermAux.dot_mem_SSpan p),
    germDiff_dot, add_zero]

theorem germDiff_coordinateResidual_coordinate_transport
    (a : Fin (r + 1 + 1)) :
    (fun y => germDiff (-coordinateDirection a) (coordinateResidual r)
      (permutedInputLinearEquiv (Equiv.swap 0 a) y)) =
      germDiff (fun _ : Fin (r + 1) => (1 : ℝ)) (coordinateResidual r) := by
  have h := germDiff_coordinateResidual_permutedInputLinearEquiv (r := r)
    (Equiv.swap 0 a) (fun _ : Fin (r + 1) => (1 : ℝ))
  rwa [permutedInputLinearEquiv_apply, permutedInput_swap_zero_one] at h

/-- A lower-span bound in the canonical all-ones direction transfers to every
scalar multiple of every coordinate direction. -/
theorem germDiff_coordinateResidual_smul_coordinate_mem_LSpan
    (a : Fin (r + 1 + 1)) (t : ℝ) {k : ℕ}
    (hcanonical : germDiff (fun _ : Fin (r + 1) => (1 : ℝ))
      (coordinateResidual r) ∈ LSpan (r + 1) k) :
    germDiff (t • coordinateDirection a) (coordinateResidual r) ∈ LSpan (r + 1) k := by
  let L := permutedInputLinearEquiv (Equiv.swap 0 a)
  have hcomp : (fun y => germDiff (-coordinateDirection a) (coordinateResidual r) (L y)) ∈
      LSpan (r + 1) k := by
    rw [germDiff_coordinateResidual_coordinate_transport]
    exact hcanonical
  have hneg : germDiff (-coordinateDirection a) (coordinateResidual r) ∈
      LSpan (r + 1) k :=
    (comp_linearEquiv_mem_LSpan_iff L).mp hcomp
  have hpos : germDiff (coordinateDirection a) (coordinateResidual r) ∈
      LSpan (r + 1) k := by
    have hn := Submodule.neg_mem (LSpan (r + 1) k) hneg
    simpa only [germDiff_eq_sub, neg_neg, neg_sub] using hn
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hscale := germDiff_pos_smul (coordinateResidual_mem_SSpan r)
      (neg_pos.mpr ht) (-coordinateDirection a)
    have he : t • coordinateDirection a = (-t) • (-coordinateDirection a) := by
      simp only [smul_neg, neg_smul, neg_neg]
    rw [he, hscale]
    exact hneg
  · simp only [zero_smul, germDiff_eq_sub, neg_zero, sub_self]
    exact Submodule.zero_mem _
  · rw [germDiff_pos_smul (coordinateResidual_mem_SSpan r) ht]
    exact hpos

end MaxNN.Caterpillar
