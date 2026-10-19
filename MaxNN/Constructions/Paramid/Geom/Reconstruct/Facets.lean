import MaxNN.Constructions.Paramid.Geom.Reconstruct.SimplexCut
import MaxNN.Constructions.Paramid.Geom.Sweep
import Mathlib.Algebra.CharZero.Infinite

/-!
# Facet data of a simplex: translations, generic directions, facet normals
(helper of `Geom/Reconstruct.lean`)

Let `p : Fin (m + 1) → ℝ^m` be affinely independent, `β_j` its barycentric coordinates
(`simplexBasis p hp`), `baryLin p hp v j = (β_j)'(v)` their rates along `v`, `F_j` the facet
opposite `p_j`, and `facetSign p hp v j = − sign (β_j)'(v)` (`Reconstruct/SimplexCut/Bary.lean`).
This file collects the facet facts that the completeness step (`Geom/Complete.lean`, blueprint
section M-Complete) needs around `simplex_reconstruct`:

* **Translations.**  `ReconstructAux.affineIndependent_add_const`, `baryLin_add_const`,
  `facetSign_add_const`: translating all vertices changes neither the rates nor the facet signs;
  `ReconstructAux.sweep_hS_image_add_smul`: translating a point set by `c • v` adds
  `c · relu ⟨v, ·⟩` to its sweep.
* **Segments.**  `sum_facetSign_of_dim_one`: for `m = 1` the two facet signs sum to zero.
* **Generic directions.**  `coord_linear_ne_zero` (each `(β_j)'` is a nonzero functional for
  `m ≥ 1`), and `exists_forall_baryLin_ne_zero`, `exists_forall_facetSign_ne_zero`: finitely many
  simplices have a common direction along which none of their facets is vertical
  (from `ReconstructAux.exists_forall_ne_zero_of_ne_zero`: finitely many nonzero linear
  functionals on `ℝ^m` have a common non-root).
* **Facet normals.**  `facetNormal p hp j`, the inner normal of `F_j` with
  `⟨facetNormal p hp j, x⟩ = (β_j)'(x)` (`dot_facetNormal`); it takes the value `−β_j(0)` on `F_j`
  and `1 − β_j(0)` at `p_j` (`dot_facetNormal_vertex`), is nonzero (`facetNormal_ne_zero`), and
  `facetSign p hp v j = − sign ⟨facetNormal p hp j, v⟩`
  (`facetSign_eq_neg_sign_dot_facetNormal`).  The face of the simplex in the outer normal
  direction `−n_j` is `F_j` (`face_neg_facetNormal`), in the inner normal direction `n_j` it is
  the vertex `p_j` (`face_facetNormal`).

Generic helpers live in the sub-namespace `MaxNN.ParamidGeom.ReconstructAux`.
-/

namespace MaxNN.ParamidGeom

open BigOperators

noncomputable section

variable {m : ℕ}

/-! ## Generic helpers -/

namespace ReconstructAux

/-- Sweep data exist only in positive dimension. -/
theorem one_le_of_dot_eq_one {v w : Fin m → ℝ} (hvw : dot w v = 1) : 1 ≤ m := by
  by_contra h
  push_neg at h
  have hm : m = 0 := by omega
  subst hm
  simp [dot] at hvw

theorem exists_ne_of_one_le (hm : 1 ≤ m) (j : Fin (m + 1)) : ∃ k : Fin (m + 1), k ≠ j := by
  have hne : (Finset.univ.erase j).Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
    omega
  obtain ⟨k, hk⟩ := hne
  exact ⟨k, Finset.ne_of_mem_erase hk⟩

theorem dot_neg_left (u x : Fin m → ℝ) : dot (-u) x = -dot u x := by
  rw [show -u = (-1 : ℝ) • u by rw [neg_one_smul], SupportCut.dot_smul_left]
  ring

/-- Translating all vertices by `t` keeps them affinely independent. -/
theorem affineIndependent_add_const {p : Fin (m + 1) → Fin m → ℝ} (hp : AffineIndependent ℝ p)
    (t : Fin m → ℝ) : AffineIndependent ℝ (fun i => p i + t) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin (m + 1))] at hp ⊢
  convert hp using 1
  funext i
  simp only [vsub_eq_sub, add_sub_add_right_eq_sub]

/-- Translating a nonempty point set by `c • v` adds `c · relu ⟨v, ·⟩` to its sweep. -/
theorem sweep_hS_image_add_smul {v w : Fin m → ℝ} (hvw : dot w v = 1) {G : Finset (Fin m → ℝ)}
    (hG : G.Nonempty) (c : ℝ) (y : Fin m → ℝ) :
    sweep v w (hS (G.image (fun x => x + c • v))) y =
      sweep v w (hS G) y + c * relu (dot v y) := by
  have e : hS (G.image (fun x => x + c • v)) = hS G + c • dot v := by
    funext ξ
    rw [Sweep.hS_image_add_smul hG]
    rfl
  rw [e, sweep_add, sweep_smul, sweep_dot_self hvw]
  rfl

/-- A finite family of nonzero linear functionals on `ℝ^m` has a common non-root. -/
theorem exists_forall_ne_zero_of_ne_zero {κ : Type*} (s : Finset κ)
    (φ : κ → (Fin m → ℝ) →ₗ[ℝ] ℝ) (hφ : ∀ k ∈ s, φ k ≠ 0) :
    ∃ v : Fin m → ℝ, ∀ k ∈ s, φ k v ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun k hk => absurd hk (Finset.not_mem_empty k)⟩
  | @insert a s _ ih =>
    obtain ⟨v, hv⟩ := ih fun k hk => hφ k (Finset.mem_insert_of_mem hk)
    obtain ⟨u, hu⟩ : ∃ u, φ a u ≠ 0 := by
      by_contra h
      push_neg at h
      exact hφ a (Finset.mem_insert_self a s) (LinearMap.ext h)
    obtain ⟨t, ht⟩ := Infinite.exists_not_mem_finset
      ((insert a s).image fun k => -φ k v / φ k u)
    refine ⟨v + t • u, fun k hk => ?_⟩
    rw [map_add, map_smul, smul_eq_mul]
    intro h0
    by_cases hku : φ k u = 0
    · rw [hku, mul_zero, add_zero] at h0
      rcases Finset.mem_insert.mp hk with rfl | hks
      · exact hu hku
      · exact hv k hks h0
    · apply ht
      refine Finset.mem_image.mpr ⟨k, hk, ?_⟩
      field_simp
      linarith

end ReconstructAux

open ReconstructAux

/-! ## Translation invariance of the facet data -/

/-- The rates `(β_j)'(v)` of the barycentric coordinates are translation invariant. -/
theorem baryLin_add_const {p : Fin (m + 1) → Fin m → ℝ} (hp : AffineIndependent ℝ p)
    (t : Fin m → ℝ) (hpt : AffineIndependent ℝ (fun i => p i + t)) (v : Fin m → ℝ)
    (j : Fin (m + 1)) : baryLin (fun i => p i + t) hpt v j = baryLin p hp v j := by
  refine baryLin_eq_of_sum_smul _ hpt (baryLin p hp v) (sum_baryLin p hp v) ?_ j
  simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, sum_baryLin, zero_smul,
    add_zero, sum_baryLin_smul]

/-- Facet signs are translation invariant. -/
theorem facetSign_add_const {p : Fin (m + 1) → Fin m → ℝ} (hp : AffineIndependent ℝ p)
    (t : Fin m → ℝ) (hpt : AffineIndependent ℝ (fun i => p i + t)) (v : Fin m → ℝ)
    (j : Fin (m + 1)) : facetSign (fun i => p i + t) hpt v j = facetSign p hp v j := by
  rw [facetSign_eq, facetSign_eq, baryLin_add_const hp t hpt v j]

/-! ## Segments -/

/-- A segment (`m = 1`) has one upper and one lower facet, or two vertical ones: its facet
signs sum to zero. -/
theorem sum_facetSign_of_dim_one (p : Fin (1 + 1) → Fin 1 → ℝ) (hp : AffineIndependent ℝ p)
    (v : Fin 1 → ℝ) : ∑ j, facetSign p hp v j = 0 := by
  have h := sum_baryLin p hp v
  rw [Fin.sum_univ_two] at h ⊢
  have h1 : baryLin p hp v 1 = -baryLin p hp v 0 := by linarith
  rcases lt_trichotomy (baryLin p hp v 0) 0 with h0 | h0 | h0
  · rw [facetSign_of_neg h0, facetSign_of_pos (by rw [h1]; linarith)]
    norm_num
  · rw [facetSign_of_eq_zero h0, facetSign_of_eq_zero (by rw [h1, h0, neg_zero])]
    norm_num
  · rw [facetSign_of_pos h0, facetSign_of_neg (by rw [h1]; linarith)]
    norm_num

/-! ## Generic directions -/

/-- The linear part of a barycentric coordinate of a simplex of positive dimension is nonzero. -/
theorem coord_linear_ne_zero (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (hm : 1 ≤ m) (j : Fin (m + 1)) : ((simplexBasis p hp).coord j).linear ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := exists_ne_of_one_le hm j
  have e : ((simplexBasis p hp).coord j).linear (p j -ᵥ p k) = 1 := by
    rw [AffineMap.linearMap_vsub, coord_simplexBasis_vertex, coord_simplexBasis_vertex,
      if_pos rfl, if_neg hk.symm, vsub_eq_sub, sub_zero]
  rw [h, LinearMap.zero_apply] at e
  exact zero_ne_one e

/-- **Generic directions exist:** finitely many simplices of positive dimension have a common
direction `v` along which none of their facets is vertical. -/
theorem exists_forall_baryLin_ne_zero (hm : 1 ≤ m) {ι : Type*} [Fintype ι]
    (P : ι → Fin (m + 1) → Fin m → ℝ) (hP : ∀ i, AffineIndependent ℝ (P i)) :
    ∃ v : Fin m → ℝ, ∀ i j, baryLin (P i) (hP i) v j ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_forall_ne_zero_of_ne_zero
    (Finset.univ : Finset (ι × Fin (m + 1)))
    (fun ij => ((simplexBasis (P ij.1) (hP ij.1)).coord ij.2).linear)
    (fun ij _ => coord_linear_ne_zero (P ij.1) (hP ij.1) hm ij.2)
  exact ⟨v, fun i j => hv (i, j) (Finset.mem_univ _)⟩

/-- Generic directions, in terms of facet signs: no facet sign vanishes. -/
theorem exists_forall_facetSign_ne_zero (hm : 1 ≤ m) {ι : Type*} [Fintype ι]
    (P : ι → Fin (m + 1) → Fin m → ℝ) (hP : ∀ i, AffineIndependent ℝ (P i)) :
    ∃ v : Fin m → ℝ, ∀ i j, facetSign (P i) (hP i) v j ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_forall_baryLin_ne_zero hm P hP
  exact ⟨v, fun i j h => hv i j (facetSign_eq_zero_iff.mp h)⟩

/-! ## Facet normals -/

/-- The inner normal of the facet `F_j`: the coefficient vector of the linear part of the
barycentric coordinate `β_j`, so that `⟨facetNormal p hp j, x⟩ = (β_j)'(x)`. -/
def facetNormal (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p) (j : Fin (m + 1)) :
    Fin m → ℝ :=
  SimplexCut.dualVec ((simplexBasis p hp).coord j).linear

theorem dot_facetNormal (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (j : Fin (m + 1)) (x : Fin m → ℝ) : dot (facetNormal p hp j) x = baryLin p hp x j :=
  SimplexCut.dot_dualVec _ x

/-- `⟨n_j, ·⟩` is constant (`= −β_j(0)`) on the facet `F_j` and one more at `p_j`. -/
theorem dot_facetNormal_vertex (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (j i : Fin (m + 1)) :
    dot (facetNormal p hp j) (p i) = (if j = i then 1 else 0) - (simplexBasis p hp).coord j 0 := by
  rw [dot_facetNormal, baryLin_eq_sub, coord_simplexBasis_vertex]

theorem facetSign_eq_neg_sign_dot_facetNormal (p : Fin (m + 1) → Fin m → ℝ)
    (hp : AffineIndependent ℝ p) (v : Fin m → ℝ) (j : Fin (m + 1)) :
    facetSign p hp v j = -((SignType.sign (dot (facetNormal p hp j) v) : SignType) : ℝ) := by
  rw [facetSign_eq, dot_facetNormal]

theorem facetNormal_ne_zero (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (hm : 1 ≤ m) (j : Fin (m + 1)) : facetNormal p hp j ≠ 0 := by
  intro h
  apply coord_linear_ne_zero p hp hm j
  refine LinearMap.ext fun x => ?_
  have e := dot_facetNormal p hp j x
  rw [h, Sweep.dot_zero_left] at e
  exact e.symm

/-- The face of the simplex in the direction of the outer normal `−n_j` of `F_j` is `F_j`. -/
theorem face_neg_facetNormal (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (hm : 1 ≤ m) (j : Fin (m + 1)) :
    face (-facetNormal p hp j) (Finset.univ.image p) = (Finset.univ.erase j).image p := by
  ext x
  simp only [face, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, and_true,
    Finset.mem_erase, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨⟨i, rfl⟩, hmax⟩
    refine ⟨i, ?_, rfl⟩
    rintro rfl
    obtain ⟨k, hk⟩ := exists_ne_of_one_le hm i
    have := hmax k
    rw [dot_neg_left, dot_neg_left, dot_facetNormal_vertex, dot_facetNormal_vertex,
      if_neg hk.symm, if_pos rfl] at this
    linarith
  · rintro ⟨i, hij, rfl⟩
    refine ⟨⟨i, rfl⟩, fun k => ?_⟩
    rw [dot_neg_left, dot_neg_left, dot_facetNormal_vertex, dot_facetNormal_vertex,
      if_neg (Ne.symm hij)]
    split_ifs <;> linarith

/-- The face of the simplex in the direction of the inner normal `n_j` of `F_j` is the opposite
vertex `p_j`. -/
theorem face_facetNormal (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (j : Fin (m + 1)) : face (facetNormal p hp j) (Finset.univ.image p) = {p j} := by
  ext x
  simp only [face, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨⟨i, rfl⟩, hmax⟩
    by_contra hne
    have hij : j ≠ i := fun h => hne (by rw [h])
    have := hmax j
    rw [dot_facetNormal_vertex, dot_facetNormal_vertex, if_pos rfl, if_neg hij] at this
    linarith
  · rintro rfl
    refine ⟨⟨j, rfl⟩, fun k => ?_⟩
    rw [dot_facetNormal_vertex, dot_facetNormal_vertex, if_pos rfl]
    split_ifs <;> linarith

end

end MaxNN.ParamidGeom
