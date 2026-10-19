import MaxNN.Constructions.Paramid.Geom.Germ
import MaxNN.Constructions.Paramid.Geom.Reconstruct.Facets

/-!
# Germ differences of a simplex in its facet directions (helper for `Geom/Reconstruct.lean`)

Let `p : Fin (m + 1) → ℝ^m` be affinely independent, `P = univ.image p`, `F_j` the facet opposite
`p_j`, `n_j = facetNormal p hp j` the inner normal of `F_j` (`Reconstruct/Facets.lean`:
`⟨n_j, x⟩ = (β_j)'(x)`, the face of `P` in direction `−n_j` is `F_j`, in direction `n_j` it is
`{p_j}`), and `v` a sweep direction.  This file is the bridge between the facet signs of the
reconstruction (`simplex_reconstruct`) and the facet data `germDiff` of the flag functionals,
which the completeness step (`Geom/Complete.lean`) needs in order to group the swept facets by
their normal direction and to apply the induction hypothesis in each facet hyperplane.

* `finrank_vectorSpan_face_simplex_le`: if `u ≠ 0` is not a positive multiple of an outer
  normal `−n_j`, the face of `P` in direction `u` has affine dimension `≤ m − 2`.
* `facetDir p hp v j = ⟨n_j, v⟩⁻¹ • n_j`: the facet normal normalized against `v` (the same
  vector for the inner and the outer normal).  For a non-vertical facet `⟨facetDir, v⟩ = 1`
  (`dot_facetDir_self`); for a vertical facet `facetDir = 0` (`facetDir_of_vertical`); every
  facet has `⟨facetDir, v⟩ = 1` or sign `0` (`dot_facetDir_self_or_facetSign_eq_zero`).
  `facetDir_eq_of_eq_smul`, `facetNormal_eq_smul_of_facetDir_eq` translate between
  `facetDir p hp v j = ν` and "`n_j` is a multiple of `ν`" when `⟨ν, v⟩ = 1`; in dimension
  `m ≥ 2` two facets never share a direction (`facetDir_inj`).
* `germDiff_hS_simplex_of_facetDir_eq`: if `facetDir p hp v j = ν`, then
  `germDiff ν h_P = facetSign_j · (h_{F_j} − ⟨p_j, ·⟩)` (exactly).
* `germDiff_hS_simplex_mem_LSpan`: if `⟨ν, v⟩ = 1` and no facet has direction `ν`, then
  `germDiff ν h_P ∈ LSpan m (m − 2)`.
* `germDiff_hS_simplex_sub_mem_LSpan` (the grouping lemma, `m ≥ 2`, `⟨ν, v⟩ = 1`):
  `germDiff ν h_P − ∑_{j : facetDir p hp v j = ν} facetSign_j · h_{F_j} ∈ LSpan m (m − 2)`.
* Facets as simplices: `FacetGermAux.affineIndependent_comp_succAbove`,
  `FacetGermAux.image_univ_comp_succAbove` (`F_j = univ.image (p ∘ j.succAbove)`), and
  `dot_facetNormal_eq_of_ne`, `dot_facetDir_eq_of_ne` (the facet `F_j` lies in a hyperplane
  orthogonal to `n_j`).

Generic helpers live in the sub-namespace `MaxNN.ParamidGeom.FacetGermAux`.
-/

namespace MaxNN.ParamidGeom

open BigOperators

noncomputable section

variable {m : ℕ}

/-! ## Generic helpers -/

namespace FacetGermAux

theorem dot_single (a : Fin m → ℝ) (i : Fin m) : dot a (Pi.single i 1) = a i := by
  show Matrix.dotProduct a (Pi.single i 1) = a i
  rw [Matrix.dotProduct_single, mul_one]

/-- Vectors with the same linear form are equal. -/
theorem eq_of_forall_dot_eq {a b : Fin m → ℝ} (h : ∀ x, dot a x = dot b x) : a = b := by
  funext i
  rw [← dot_single a i, ← dot_single b i]
  exact h _

/-- `⟨u, x⟩ = ∑_i (β_i)'(x) ⟨u, p_i⟩` (`x = ∑_i (β_i)'(x) p_i`). -/
theorem dot_eq_sum_baryLin (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (u x : Fin m → ℝ) : dot u x = ∑ i, baryLin p hp x i * dot u (p i) := by
  conv_lhs => rw [← sum_baryLin_smul p hp x]
  exact SupportCut.dot_sum_smul_right u Finset.univ (fun i => baryLin p hp x i) p

/-- The face of `univ.image p` in direction `u` is the image of the maximizing indices. -/
theorem face_image_univ (p : Fin (m + 1) → Fin m → ℝ) (u : Fin m → ℝ) :
    face u (Finset.univ.image p) =
      (Finset.univ.filter fun i => ∀ l, dot u (p l) ≤ dot u (p i)).image p := by
  ext x
  rw [mem_face]
  constructor
  · rintro ⟨hx, hmax⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun l =>
      hmax (p l) (Finset.mem_image_of_mem p (Finset.mem_univ l))⟩, rfl⟩
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨Finset.mem_image_of_mem p (Finset.mem_univ i), fun q hq => ?_⟩
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hi).2 l

end FacetGermAux

open FacetGermAux

/-! ## Faces of a simplex that are not facets -/

/-- **Faces of a simplex in non-facet directions are small.**  If `u ≠ 0` is not a positive
multiple of an outer facet normal `−n_j`, the face of the simplex in direction `u` has affine
dimension `≤ m − 2`. -/
theorem finrank_vectorSpan_face_simplex_le (p : Fin (m + 1) → Fin m → ℝ)
    (hp : AffineIndependent ℝ p) {u : Fin m → ℝ} (hu : u ≠ 0)
    (hnf : ∀ (j : Fin (m + 1)) (c : ℝ), 0 < c → u ≠ c • -facetNormal p hp j) :
    FiniteDimensional.finrank ℝ
      (vectorSpan ℝ (face u (Finset.univ.image p) : Set (Fin m → ℝ))) ≤ m - 2 := by
  rw [face_image_univ]
  generalize hI : (Finset.univ.filter fun i => ∀ l, dot u (p l) ≤ dot u (p i)) = I
  have hmem : ∀ i, i ∈ I ↔ ∀ l, dot u (p l) ≤ dot u (p i) := by
    intro i
    rw [← hI, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => dot u (p i))
    Finset.univ_nonempty
  have hi0I : i0 ∈ I := (hmem i0).mpr fun l => hi0 l (Finset.mem_univ l)
  by_cases h2 : ∃ j k, j ≠ k ∧ j ∉ I ∧ k ∉ I
  · -- two vertices off the face: at most `m − 1` vertices on it
    obtain ⟨j, k, hjk, hj, hk⟩ := h2
    have hsub : I ⊆ (Finset.univ.erase j).erase k := by
      intro i hi
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩⟩
      · rintro rfl
        exact hk hi
      · rintro rfl
        exact hj hi
    have hi0j : i0 ≠ j := by
      rintro rfl
      exact hj hi0I
    have hi0k : i0 ≠ k := by
      rintro rfl
      exact hk hi0I
    have hm2 := SimplexCut.two_le_of_three_ne hi0j hi0k hjk
    have hc : ((Finset.univ.erase j).erase k).card = m - 2 + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩),
        Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
      omega
    calc FiniteDimensional.finrank ℝ
          (vectorSpan ℝ ((I.image p : Finset (Fin m → ℝ)) : Set (Fin m → ℝ)))
        ≤ FiniteDimensional.finrank ℝ (vectorSpan ℝ
            ((((Finset.univ.erase j).erase k).image p : Finset (Fin m → ℝ)) :
              Set (Fin m → ℝ))) :=
          Submodule.finrank_mono (vectorSpan_mono ℝ
            (Finset.coe_subset.mpr (Finset.image_subset_image hsub)))
      _ ≤ m - 2 := finrank_vectorSpan_image_finset_le ℝ p _ hc
  · exfalso
    push_neg at h2
    by_cases h1 : ∃ j, j ∉ I
    · -- exactly one vertex `p_j` off the face: `u` is a positive multiple of `−n_j`
      obtain ⟨j, hj⟩ := h1
      have hall : ∀ i, i ≠ j → i ∈ I := fun i hij => h2 j i (Ne.symm hij) hj
      have hval : ∀ i, i ≠ j → dot u (p i) = dot u (p i0) := fun i hij =>
        le_antisymm (hi0 i (Finset.mem_univ i)) ((hmem i).mp (hall i hij) i0)
      have hlt : dot u (p j) < dot u (p i0) := by
        by_contra hge
        push_neg at hge
        exact hj ((hmem j).mpr fun l => le_trans (hi0 l (Finset.mem_univ l)) hge)
      refine hnf j (dot u (p i0) - dot u (p j)) (by linarith) (eq_of_forall_dot_eq fun x => ?_)
      have hsplit : ∑ i, baryLin p hp x i * dot u (p i) =
          baryLin p hp x j * dot u (p j) +
            ∑ i in Finset.univ.erase j, baryLin p hp x i * dot u (p i) :=
        (Finset.add_sum_erase Finset.univ (fun i => baryLin p hp x i * dot u (p i))
          (Finset.mem_univ j)).symm
      have hs : ∑ i in Finset.univ.erase j, baryLin p hp x i * dot u (p i) =
          dot u (p i0) * ∑ i in Finset.univ.erase j, baryLin p hp x i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => by
          rw [hval i (Finset.ne_of_mem_erase hi), mul_comm]
      have hsum : ∑ i, baryLin p hp x i =
          baryLin p hp x j + ∑ i in Finset.univ.erase j, baryLin p hp x i :=
        (Finset.add_sum_erase Finset.univ (fun i => baryLin p hp x i) (Finset.mem_univ j)).symm
      have hrest : ∑ i in Finset.univ.erase j, baryLin p hp x i = -baryLin p hp x j := by
        have h0 := sum_baryLin p hp x
        rw [hsum] at h0
        linarith
      rw [SupportCut.dot_smul_left, ReconstructAux.dot_neg_left, dot_facetNormal,
        dot_eq_sum_baryLin p hp u x, hsplit, hs, hrest]
      ring
    · -- every vertex on the face: `u` is constant on the simplex, so `u = 0`
      push_neg at h1
      apply hu
      refine eq_of_forall_dot_eq fun x => ?_
      have hval : ∀ i, dot u (p i) = dot u (p i0) := fun i =>
        le_antisymm (hi0 i (Finset.mem_univ i)) ((hmem i).mp (h1 i) i0)
      have hconst : ∑ i, baryLin p hp x i * dot u (p i) =
          ∑ i, baryLin p hp x i * dot u (p i0) :=
        Finset.sum_congr rfl fun i _ => by rw [hval i]
      rw [dot_eq_sum_baryLin p hp u x, Sweep.dot_zero_left, hconst, ← Finset.sum_mul,
        sum_baryLin, zero_mul]

/-! ## Facet directions normalized against the sweep direction -/

/-- The normal of the facet `F_j` normalized against the direction `v`:
`facetDir p hp v j = ⟨n_j, v⟩⁻¹ • n_j` (equivalently `⟨−n_j, v⟩⁻¹ • (−n_j)`).  For a non-vertical
facet `⟨facetDir p hp v j, v⟩ = 1`; for a vertical facet `facetDir p hp v j = 0`. -/
def facetDir (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p) (v : Fin m → ℝ)
    (j : Fin (m + 1)) : Fin m → ℝ :=
  (dot (facetNormal p hp j) v)⁻¹ • facetNormal p hp j

section FacetDir

variable (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p) {v : Fin m → ℝ}
  {j : Fin (m + 1)}

theorem dot_facetDir_self (hv : dot (facetNormal p hp j) v ≠ 0) :
    dot (facetDir p hp v j) v = 1 := by
  rw [facetDir, SupportCut.dot_smul_left, inv_mul_cancel hv]

theorem facetDir_of_vertical (hv : dot (facetNormal p hp j) v = 0) : facetDir p hp v j = 0 := by
  rw [facetDir, hv, inv_zero, zero_smul]

/-- Every facet either has a direction normalized against `v` or carries the sign `0`. -/
theorem dot_facetDir_self_or_facetSign_eq_zero :
    dot (facetDir p hp v j) v = 1 ∨ facetSign p hp v j = 0 := by
  by_cases hv : dot (facetNormal p hp j) v = 0
  · right
    rw [facetSign_eq_neg_sign_dot_facetNormal, hv, sign_zero, SignType.coe_zero, neg_zero]
  · exact Or.inl (dot_facetDir_self p hp hv)

/-- If `⟨ν, v⟩ = 1` and `ν` is a multiple of `n_j`, then `ν` is the direction of `F_j`. -/
theorem facetDir_eq_of_eq_smul {ν : Fin m → ℝ} (hν : dot ν v = 1) {c : ℝ}
    (h : ν = c • facetNormal p hp j) : facetDir p hp v j = ν := by
  have hd : c * dot (facetNormal p hp j) v = 1 := by
    rw [← SupportCut.dot_smul_left, ← h, hν]
  have hinv : (dot (facetNormal p hp j) v)⁻¹ = c := by
    apply inv_eq_of_mul_eq_one_right
    rw [mul_comm]
    exact hd
  rw [facetDir, hinv, h]

/-- If `ν` (with `⟨ν, v⟩ = 1`) is the direction of `F_j`, then `F_j` is not vertical and
`n_j = ⟨n_j, v⟩ • ν`. -/
theorem facetNormal_eq_smul_of_facetDir_eq {ν : Fin m → ℝ} (hν : dot ν v = 1)
    (h : facetDir p hp v j = ν) :
    dot (facetNormal p hp j) v ≠ 0 ∧ facetNormal p hp j = dot (facetNormal p hp j) v • ν := by
  have hd0 : dot (facetNormal p hp j) v ≠ 0 := by
    intro h0
    rw [facetDir_of_vertical p hp h0] at h
    rw [← h, Sweep.dot_zero_left] at hν
    exact zero_ne_one hν
  refine ⟨hd0, ?_⟩
  rw [← h, facetDir, smul_smul, mul_inv_cancel hd0, one_smul]

end FacetDir

/-- **Two facets of a simplex of dimension `m ≥ 2` are not parallel:** they have different
directions. -/
theorem facetDir_inj (hm : 2 ≤ m) (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    {v ν : Fin m → ℝ} (hν : dot ν v = 1) {j k : Fin (m + 1)} (hj : facetDir p hp v j = ν)
    (hk : facetDir p hp v k = ν) : j = k := by
  by_contra hjk
  obtain ⟨hj0, hjn⟩ := facetNormal_eq_smul_of_facetDir_eq p hp hν hj
  obtain ⟨-, hkn⟩ := facetNormal_eq_smul_of_facetDir_eq p hp hν hk
  have hc : ((Finset.univ.erase j).erase k).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩),
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
    omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp
    (show 0 < ((Finset.univ.erase j).erase k).card by rw [hc]; omega)
  obtain ⟨hlj, hlk⟩ := SimplexCut.ne_ne_of_mem_erase_erase hl
  have e1 : dot (facetNormal p hp j) (p k) = dot (facetNormal p hp j) (p l) := by
    rw [dot_facetNormal_vertex, dot_facetNormal_vertex, if_neg hjk, if_neg (Ne.symm hlj)]
  have e2 : dot (facetNormal p hp k) (p k) = dot (facetNormal p hp k) (p l) + 1 := by
    rw [dot_facetNormal_vertex, dot_facetNormal_vertex, if_pos rfl, if_neg (Ne.symm hlk)]
    ring
  rw [hjn, SupportCut.dot_smul_left, SupportCut.dot_smul_left] at e1
  rw [hkn, SupportCut.dot_smul_left, SupportCut.dot_smul_left] at e2
  have e1' := mul_left_cancel₀ hj0 e1
  rw [e1'] at e2
  linarith

/-! ## The facet datum of a simplex in a facet direction -/

/-- **Germ difference of a simplex in the direction of one of its facets.**  If
`facetDir p hp v j = ν`, then `germDiff ν h_P = facetSign_j · (h_{F_j} − ⟨p_j, ·⟩)`: for an upper
facet `ν` is a positive multiple of the outer normal and the two opposite faces are `F_j` and
`{p_j}`; for a lower facet they are exchanged; for a vertical facet `ν = 0` and both sides
vanish. -/
theorem germDiff_hS_simplex_of_facetDir_eq (hm : 1 ≤ m) (p : Fin (m + 1) → Fin m → ℝ)
    (hp : AffineIndependent ℝ p) {v ν : Fin m → ℝ} {j : Fin (m + 1)}
    (hj : facetDir p hp v j = ν) :
    germDiff ν (hS (Finset.univ.image p)) =
      facetSign p hp v j • (hS ((Finset.univ.erase j).image p) - dot (p j)) := by
  have hne : (Finset.univ.image p).Nonempty := Finset.univ_nonempty.image p
  rw [germDiff_hS hne, facetSign_eq_neg_sign_dot_facetNormal]
  have hνeq : ν = (dot (facetNormal p hp j) v)⁻¹ • facetNormal p hp j := hj.symm
  rcases lt_trichotomy (dot (facetNormal p hp j) v) 0 with hd | hd | hd
  · -- upper facet: `ν` is a positive multiple of the outer normal `−n_j`
    have hc : 0 < -(dot (facetNormal p hp j) v)⁻¹ := neg_pos.mpr (inv_lt_zero.mpr hd)
    have e1 : ν = (-(dot (facetNormal p hp j) v)⁻¹) • -facetNormal p hp j := by
      rw [hνeq, neg_smul_neg]
    have e2 : -ν = (-(dot (facetNormal p hp j) v)⁻¹) • facetNormal p hp j := by
      rw [hνeq, neg_smul]
    rw [e2, face_smul_of_pos hc, face_facetNormal, e1, face_smul_of_pos hc,
      face_neg_facetNormal p hp hm, sign_neg hd, SignType.coe_neg_one, neg_neg, one_smul,
      GermAux.hS_singleton]
  · -- vertical facet: `ν = 0`
    have hν0 : ν = 0 := by
      rw [hνeq, hd, inv_zero, zero_smul]
    rw [hν0, neg_zero, sub_self, hd, sign_zero, SignType.coe_zero, neg_zero, zero_smul]
  · -- lower facet: `ν` is a positive multiple of the inner normal `n_j`
    have hc : 0 < (dot (facetNormal p hp j) v)⁻¹ := inv_pos.mpr hd
    have e2 : -ν = (dot (facetNormal p hp j) v)⁻¹ • -facetNormal p hp j := by
      rw [hνeq, smul_neg]
    rw [e2, face_smul_of_pos hc, face_neg_facetNormal p hp hm, hνeq, face_smul_of_pos hc,
      face_facetNormal, sign_pos hd, SignType.coe_one, GermAux.hS_singleton, neg_one_smul,
      neg_sub]

/-- **Germ difference of a simplex in a direction that is not a facet direction.**  If
`⟨ν, v⟩ = 1` and no facet of the simplex has direction `ν`, then
`germDiff ν h_P ∈ LSpan m (m − 2)`. -/
theorem germDiff_hS_simplex_mem_LSpan (p : Fin (m + 1) → Fin m → ℝ)
    (hp : AffineIndependent ℝ p) {v ν : Fin m → ℝ} (hν : dot ν v = 1)
    (hno : ∀ j, facetDir p hp v j ≠ ν) :
    germDiff ν (hS (Finset.univ.image p)) ∈ LSpan m (m - 2) := by
  have hne : (Finset.univ.image p).Nonempty := Finset.univ_nonempty.image p
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [Sweep.dot_zero_left] at hν
    exact zero_ne_one hν
  rw [germDiff_hS hne]
  refine Submodule.sub_mem _ (SimplexCut.hS_mem_LSpan_of_finrank_le ?_)
    (SimplexCut.hS_mem_LSpan_of_finrank_le ?_)
  · refine finrank_vectorSpan_face_simplex_le p hp hν0 fun j c _ h => hno j ?_
    have h' : ν = (-c) • facetNormal p hp j := by
      rw [h, smul_neg, neg_smul]
    exact facetDir_eq_of_eq_smul p hp hν h'
  · refine finrank_vectorSpan_face_simplex_le p hp (neg_ne_zero.mpr hν0) fun j c _ h => hno j ?_
    have h' : ν = c • facetNormal p hp j := by
      rw [← neg_neg ν, h, smul_neg, neg_neg]
    exact facetDir_eq_of_eq_smul p hp hν h'

/-- **The grouping lemma.**  For a simplex of dimension `m ≥ 2` and a direction `ν` with
`⟨ν, v⟩ = 1`, the facet datum `germDiff ν h_P` is, modulo `LSpan m (m − 2)`, the signed sum of
the support functions of the facets of direction `ν` (at most one facet):
`germDiff ν h_P − ∑_{j : facetDir p hp v j = ν} facetSign_j · h_{F_j} ∈ LSpan m (m − 2)`. -/
theorem germDiff_hS_simplex_sub_mem_LSpan (hm : 2 ≤ m) (p : Fin (m + 1) → Fin m → ℝ)
    (hp : AffineIndependent ℝ p) {v ν : Fin m → ℝ} (hν : dot ν v = 1) :
    germDiff ν (hS (Finset.univ.image p)) -
        ∑ j in Finset.univ.filter (fun j => facetDir p hp v j = ν),
          facetSign p hp v j • hS ((Finset.univ.erase j).image p) ∈ LSpan m (m - 2) := by
  by_cases h : ∃ j, facetDir p hp v j = ν
  · obtain ⟨j, hj⟩ := h
    have hfilter : Finset.univ.filter (fun k => facetDir p hp v k = ν) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hk => facetDir_inj hm p hp hν hk hj, fun hk => by rw [hk]; exact hj⟩
    rw [hfilter, Finset.sum_singleton, germDiff_hS_simplex_of_facetDir_eq (by omega) p hp hj,
      smul_sub, sub_sub_cancel_left]
    refine Submodule.neg_mem _ (Submodule.smul_mem _ _ ?_)
    rw [← GermAux.hS_singleton]
    refine SimplexCut.hS_mem_LSpan_of_finrank_le ?_
    rw [Finset.coe_singleton, vectorSpan_singleton, finrank_bot]
    exact Nat.zero_le _
  · push_neg at h
    rw [Finset.filter_false_of_mem fun j _ => h j, Finset.sum_empty, sub_zero]
    exact germDiff_hS_simplex_mem_LSpan p hp hν h

/-! ## Facets as simplices -/

/-- The facet `F_j` lies in a hyperplane orthogonal to `n_j`. -/
theorem dot_facetNormal_eq_of_ne (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    {i j k : Fin (m + 1)} (hij : i ≠ j) (hkj : k ≠ j) :
    dot (facetNormal p hp j) (p i) = dot (facetNormal p hp j) (p k) := by
  rw [dot_facetNormal_vertex, dot_facetNormal_vertex, if_neg (Ne.symm hij), if_neg (Ne.symm hkj)]

/-- The facet `F_j` lies in a hyperplane orthogonal to its direction. -/
theorem dot_facetDir_eq_of_ne (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (v : Fin m → ℝ) {i j k : Fin (m + 1)} (hij : i ≠ j) (hkj : k ≠ j) :
    dot (facetDir p hp v j) (p i) = dot (facetDir p hp v j) (p k) := by
  rw [facetDir, SupportCut.dot_smul_left, SupportCut.dot_smul_left,
    dot_facetNormal_eq_of_ne p hp hij hkj]

namespace FacetGermAux

/-- The vertices of a facet of a simplex are affinely independent. -/
theorem affineIndependent_comp_succAbove {n : ℕ} {p : Fin (n + 1) → Fin m → ℝ}
    (hp : AffineIndependent ℝ p) (j : Fin (n + 1)) : AffineIndependent ℝ (p ∘ j.succAbove) :=
  hp.comp_embedding ⟨j.succAbove, Fin.succAbove_right_injective⟩

/-- The facet opposite `p_j`, indexed by `Fin n` through `j.succAbove`. -/
theorem image_univ_comp_succAbove {n : ℕ} (p : Fin (n + 1) → Fin m → ℝ) (j : Fin (n + 1)) :
    Finset.univ.image (p ∘ j.succAbove) = (Finset.univ.erase j).image p := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, and_true, Finset.mem_erase,
    Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨j.succAbove i, Fin.succAbove_ne j i, rfl⟩
  · rintro ⟨i, hij, rfl⟩
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hij
    exact ⟨z, by rw [hz]⟩

end FacetGermAux

end

end MaxNN.ParamidGeom
