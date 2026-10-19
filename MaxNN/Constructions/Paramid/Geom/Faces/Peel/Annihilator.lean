import MaxNN.Constructions.Paramid.Geom.Faces.Peel.Generic
import MaxNN.Constructions.Paramid.Geom.Reconstruct.SimplexCut.Bary
import MaxNN.PolyhedralGeometry.SupportCut.Dot
import Mathlib.LinearAlgebra.Dual

/-!
# Annihilators in `ℝ^m` and separating directions (helper of `Geom/Faces/Peel.lean`)

For a subspace `W` of `ℝ^m`, `ann W = {e | ⟨e, w⟩ = 0 for all w ∈ W}` is its annihilator under
`dot`: the directions `e` for which `⟨e, ·⟩` is constant on every translate of `W`.

* `exists_mem_ann_dot_ne_zero`: a vector `x ∉ W` is detected by the annihilator, i.e. some
  `e ∈ ann W` has `⟨e, x⟩ ≠ 0` (Mathlib's `Subspace.dualAnnihilator_dualCoannihilator_eq`, with
  functionals turned into vectors by `SimplexCut.dualVec`).
* `exists_mem_ann_forall_dot_ne_zero`: one `e ∈ ann W` detects finitely many vectors outside `W`
  at once (common non-root on the vector space `ann W`, `Faces/Peel/Generic.lean`).
* `exists_sep_dir`: **separating directions.**  Let `𝒟` be a finite set of subspaces of the same
  dimension `k`, `W ∈ 𝒟`, and `U` a subspace of dimension `> k`.  Some `e ∈ ann W` is not in
  `ann W'` for any other `W' ∈ 𝒟`, and not in `ann U`.  (Proof of Lemma P in
  `work/depth2_simplex/smallest/PLAN_SMALLEST_GENERAL_N_2026-10-14.md`, Section 4.3: `W' ⊄ W`
  because the dimensions agree and `W' ≠ W`, `U ⊄ W` because `dim U > dim W`.)
-/

namespace MaxNN.ParamidGeom.Faces.PeelAux

open BigOperators FiniteDimensional

variable {m : ℕ}

/-! ## The annihilator -/

/-- The annihilator `{e | ⟨e, w⟩ = 0 for all w ∈ W}` of a subspace `W` of `ℝ^m`. -/
def ann (W : Submodule ℝ (Fin m → ℝ)) : Submodule ℝ (Fin m → ℝ) where
  carrier := {e | ∀ w ∈ W, dot e w = 0}
  add_mem' := by
    intro a b ha hb w hw
    show dot (a + b) w = 0
    rw [SupportCut.dot_add_left, ha w hw, hb w hw, add_zero]
  zero_mem' := by
    intro w _
    show dot (0 : Fin m → ℝ) w = 0
    rw [← zero_smul ℝ (0 : Fin m → ℝ), SupportCut.dot_smul_left, zero_mul]
  smul_mem' := by
    intro c e he w hw
    show dot (c • e) w = 0
    rw [SupportCut.dot_smul_left, he w hw, mul_zero]

theorem mem_ann {W : Submodule ℝ (Fin m → ℝ)} {e : Fin m → ℝ} :
    e ∈ ann W ↔ ∀ w ∈ W, dot e w = 0 :=
  Iff.rfl

/-- A vector outside `W` is detected by the annihilator of `W`. -/
theorem exists_mem_ann_dot_ne_zero {W : Submodule ℝ (Fin m → ℝ)} {x : Fin m → ℝ} (hx : x ∉ W) :
    ∃ e ∈ ann W, dot e x ≠ 0 := by
  have hx' : x ∉ W.dualAnnihilator.dualCoannihilator := by
    rwa [Subspace.dualAnnihilator_dualCoannihilator_eq]
  rw [Submodule.mem_dualCoannihilator] at hx'
  push_neg at hx'
  obtain ⟨φ, hφW, hφx⟩ := hx'
  rw [Submodule.mem_dualAnnihilator] at hφW
  refine ⟨SimplexCut.dualVec φ, fun w hw => ?_, ?_⟩
  · rw [SimplexCut.dot_dualVec]
    exact hφW w hw
  · rw [SimplexCut.dot_dualVec]
    exact hφx

/-- One direction of the annihilator of `W` detects finitely many vectors outside `W`. -/
theorem exists_mem_ann_forall_dot_ne_zero (W : Submodule ℝ (Fin m → ℝ))
    (Z : Finset (Fin m → ℝ)) (hZ : ∀ z ∈ Z, z ∉ W) :
    ∃ e ∈ ann W, ∀ z ∈ Z, dot e z ≠ 0 := by
  have hφ : ∀ z ∈ Z, (SupportCut.dotL z).comp (ann W).subtype ≠ 0 := by
    intro z hz h0
    obtain ⟨e, he, hez⟩ := exists_mem_ann_dot_ne_zero (hZ z hz)
    have h1 : dot z e = 0 := LinearMap.congr_fun h0 ⟨e, he⟩
    exact hez (by rw [SupportCut.dot_comm]; exact h1)
  obtain ⟨v, hv⟩ := exists_forall_apply_ne_zero Z _ hφ
  refine ⟨v, v.2, fun z hz => ?_⟩
  have h : dot z (v : Fin m → ℝ) ≠ 0 := hv z hz
  rwa [SupportCut.dot_comm] at h

/-! ## Separating directions -/

/-- **Separating directions.**  Let `𝒟` be a finite set of subspaces of `ℝ^m`, all of dimension
`k`, let `W ∈ 𝒟`, and let `U` be a subspace of dimension `> k`.  Some `e` annihilating `W` is not
constant along `U` and not constant along any other member of `𝒟`. -/
theorem exists_sep_dir {𝒟 : Finset (Submodule ℝ (Fin m → ℝ))} {k : ℕ}
    (h𝒟 : ∀ W ∈ 𝒟, finrank ℝ W = k) {W : Submodule ℝ (Fin m → ℝ)} (hW : W ∈ 𝒟)
    {U : Submodule ℝ (Fin m → ℝ)} (hU : k < finrank ℝ U) :
    ∃ e ∈ ann W, (∃ w ∈ U, dot e w ≠ 0) ∧ ∀ W' ∈ 𝒟, W' ≠ W → ∃ w ∈ W', dot e w ≠ 0 := by
  classical
  -- `U ⊄ W`, since `dim U > dim W`
  obtain ⟨x, hxU, hxW⟩ : ∃ x ∈ U, x ∉ W := by
    by_contra h
    push_neg at h
    have hle : finrank ℝ U ≤ finrank ℝ W := Submodule.finrank_mono fun y hy => h y hy
    rw [h𝒟 W hW] at hle
    omega
  -- `W' ⊄ W` for the other members, since the dimensions agree
  have hout : ∀ W' ∈ 𝒟.erase W, ∃ w ∈ W', w ∉ W := by
    intro W' hW'
    obtain ⟨hne, hW'𝒟⟩ := Finset.mem_erase.mp hW'
    by_contra h
    push_neg at h
    exact hne (FiniteDimensional.eq_of_le_of_finrank_eq (fun y hy => h y hy)
      (by rw [h𝒟 W' hW'𝒟, h𝒟 W hW]))
  choose! w hwW' hwW using hout
  obtain ⟨e, heW, he⟩ :=
    exists_mem_ann_forall_dot_ne_zero W (insert x ((𝒟.erase W).image w)) (by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hxW
      · obtain ⟨W', hW', rfl⟩ := Finset.mem_image.mp hz
        exact hwW W' hW')
  refine ⟨e, heW, ⟨x, hxU, he x (Finset.mem_insert_self _ _)⟩, fun W' hW' hne => ?_⟩
  have hmem : W' ∈ 𝒟.erase W := Finset.mem_erase.mpr ⟨hne, hW'⟩
  exact ⟨w W', hwW' W' hmem,
    he _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem w hmem))⟩

end MaxNN.ParamidGeom.Faces.PeelAux
