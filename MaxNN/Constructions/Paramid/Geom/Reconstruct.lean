import MaxNN.Constructions.Paramid.Geom.Sweep
import MaxNN.Constructions.Paramid.Geom.Reconstruct.SimplexCut
import MaxNN.Constructions.Paramid.Geom.Reconstruct.Facets
import MaxNN.Constructions.Paramid.Geom.Reconstruct.FacetGerm

/-!
# The simplex sweep reconstruction (module M-Reconstruct)

Module `M-Reconstruct` of the geometric core (`work/depth2_simplex/lean_core/BLUEPRINT.md`;
paper level: `work/depth2_simplex/CONSTRUCTIVE_SWEEP_RECONSTRUCTION_2026-10-13.md`, Section 3,
algorithm VCR specialised to simplices).

Let `p : Fin (m + 1) → ℝ^m` be affinely independent (an `m`-simplex `P = conv p`), `β_j` its
barycentric coordinates, `F_j = (univ.erase j).image p` the facet opposite `p_j`, and let
`v, w` be sweep data (`⟨w, v⟩ = 1`, `Geom/Sweep.lean`).

## The blueprint statements

Both are proved in the helper `Geom/Reconstruct/SimplexCut.lean` and exported from this module
under exactly the blueprint names (namespace `MaxNN.ParamidGeom`):

* `facetSign p hp v j = −sign ((β_j).linear v)` (`Reconstruct/SimplexCut/Bary.lean`): `+1` for an
  upper facet, `−1` for a lower facet, `0` for a vertical facet.
* `simplex_reconstruct (hm : 1 ≤ m) p hp v w (hvw : ⟨w, v⟩ = 1) (hhigh : ∀ i, 0 < ⟨w, p i⟩)`:
  `h_P − ∑_j facetSign p hp v j · 𝒯 h_{F_j} ∈ LSpan m (m − 1)`, `𝒯 = sweep v w`.
  (The first argument is named `_hm` there: it is implied by `⟨w, v⟩ = 1`.)

## Added in this file

* `simplex_reconstruct_any_height`: the same conclusion **without the height hypothesis** (and
  without `1 ≤ m`).  The ridge-cut induction of the helper only uses heights to place the swept
  sections of the cut facets in `LSpan m (m − 1)`; the sweep raises the dimension by at most one
  for every nonempty point set (`sweep_hS_mem_LSpan`, which absorbs the translation (S4)), so the
  induction goes through verbatim.  Downstream (`Geom/Complete.lean`) this removes the
  "translate up by `c v`" step.

## Facet data (helper `Geom/Reconstruct/Facets.lean`, exported through this module)

* translations: `ReconstructAux.affineIndependent_add_const`, `baryLin_add_const`,
  `facetSign_add_const`, `ReconstructAux.sweep_hS_image_add_smul`;
* segments: `sum_facetSign_of_dim_one` (for `m = 1` the facet signs sum to zero);
* generic directions: `exists_forall_baryLin_ne_zero`, `exists_forall_facetSign_ne_zero`
  (finitely many simplices have a common direction with no vertical facet);
* facet normals: `facetNormal p hp j` (inner normal of `F_j`, `⟨n_j, x⟩ = (β_j)'(x)`),
  `facetSign_eq_neg_sign_dot_facetNormal`, `facetNormal_ne_zero`, and the faces of the simplex
  in the normal directions, `face_neg_facetNormal` (`= F_j`) and `face_facetNormal` (`= {p_j}`).

## Facet data versus germ differences (helper `Geom/Reconstruct/FacetGerm.lean`)

The bridge between the facet signs of the reconstruction and the facet data `germDiff` of the flag
functionals, used in `Geom/Complete.lean` to group the swept facets by their normal direction:

* `finrank_vectorSpan_face_simplex_le`: a face of the simplex in a direction `u ≠ 0` that is not a
  positive multiple of an outer facet normal `−n_j` has dimension `≤ m − 2`;
* `facetDir p hp v j = ⟨n_j, v⟩⁻¹ • n_j` (the facet normal normalized against `v`; `0` for a
  vertical facet), `dot_facetDir_self_or_facetSign_eq_zero`, `facetDir_eq_of_eq_smul`,
  `facetNormal_eq_smul_of_facetDir_eq`, and `facetDir_inj` (`m ≥ 2`: two facets never share a
  direction);
* `germDiff_hS_simplex_of_facetDir_eq`: `germDiff ν h_P = facetSign_j · (h_{F_j} − ⟨p_j, ·⟩)` if
  `facetDir p hp v j = ν`;
* `germDiff_hS_simplex_mem_LSpan`: `germDiff ν h_P ∈ LSpan m (m − 2)` if `⟨ν, v⟩ = 1` and no
  facet has direction `ν`;
* `germDiff_hS_simplex_sub_mem_LSpan` (grouping lemma, `m ≥ 2`, `⟨ν, v⟩ = 1`):
  `germDiff ν h_P − ∑_{j : facetDir p hp v j = ν} facetSign_j · h_{F_j} ∈ LSpan m (m − 2)`;
* facets as simplices: `FacetGermAux.affineIndependent_comp_succAbove`,
  `FacetGermAux.image_univ_comp_succAbove`, `dot_facetNormal_eq_of_ne`, `dot_facetDir_eq_of_ne`.
-/

namespace MaxNN.ParamidGeom

open BigOperators

noncomputable section

variable {m : ℕ}

/-! ## The reconstruction for arbitrary heights -/

/-- **The simplex reconstruction, for arbitrary heights.**  For an affinely independent
`p : Fin (m + 1) → ℝ^m` and sweep data `⟨w, v⟩ = 1`,
`h_P − ∑_j facetSign p hp v j · 𝒯 h_{F_j} ∈ LSpan m (m − 1)`.  Strengthens
`simplex_reconstruct` (no height hypothesis, no `1 ≤ m`). -/
theorem simplex_reconstruct_any_height (p : Fin (m + 1) → Fin m → ℝ)
    (hp : AffineIndependent ℝ p) (v w : Fin m → ℝ) (hvw : dot w v = 1) :
    (fun y => hS (Finset.univ.image p) y -
      ∑ j, facetSign p hp v j * sweep v w (hS ((Finset.univ.erase j).image p)) y) ∈
        LSpan m (m - 1) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [dot] at hvw
  suffices H : ∀ n : ℕ, ∀ (P : Fin (m + 1) → Fin m → ℝ) (hP : AffineIndependent ℝ P),
      (Finset.univ.filter fun i => baryLin P hP v i ≠ 0).card ≤ n →
      (fun y => hS (Finset.univ.image P) y -
        ∑ j, facetSign P hP v j * sweep v w (hS ((Finset.univ.erase j).image P)) y) ∈
          LSpan m (m - 1) by
    exact H _ p hp le_rfl
  intro n
  induction n with
  | zero =>
    intro P hP hcard
    exfalso
    obtain ⟨j, hj⟩ := exists_baryLin_ne_zero P hP hv0
    have hpos : 0 < (Finset.univ.filter fun i => baryLin P hP v i ≠ 0).card :=
      Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    have h0 := Nat.le_zero.mp hcard
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  | succ n ih =>
    intro P hP hcard
    by_cases hpair : ∃ j k, j ≠ k ∧ 0 < baryLin P hP v j * baryLin P hP v k
    · -- two upper or two lower facets: cut through their common ridge
      obtain ⟨j, k, hjk, hsame⟩ := hpair
      have hj0 : baryLin P hP v j ≠ 0 := by
        intro h
        rw [h, zero_mul] at hsame
        exact lt_irrefl 0 hsame
      have hk0 : baryLin P hP v k ≠ 0 := by
        intro h
        rw [h, mul_zero] at hsame
        exact lt_irrefl 0 hsame
      have h1 := affineIndependent_ridgeLeft P hP v j k hjk hsame
      have h2 := affineIndependent_ridgeRight P hP v j k hjk hsame
      have hjmem : j ∈ Finset.univ.filter fun i => baryLin P hP v i ≠ 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj0⟩
      have hkmem : k ∈ Finset.univ.filter fun i => baryLin P hP v i ≠ 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk0⟩
      have hc1 : (Finset.univ.filter fun i =>
          baryLin (Function.update P k (ridgePoint P hP v j k)) h1 v i ≠ 0).card ≤ n := by
        rw [filter_ridgeLeft P hP v hjk hsame h1, Finset.card_erase_of_mem hjmem]
        omega
      have hc2 : (Finset.univ.filter fun i =>
          baryLin (Function.update P j (ridgePoint P hP v j k)) h2 v i ≠ 0).card ≤ n := by
        rw [filter_ridgeRight P hP v hjk hsame h2, Finset.card_erase_of_mem hkmem]
        omega
      have hR1 := ih _ h1 hc1
      have hR2 := ih _ h2 hc2
      have hsec : hS (insert (ridgePoint P hP v j k) (((Finset.univ.erase j).erase k).image P)) ∈
          LSpan m (m - 1) :=
        SimplexCut.hS_mem_LSpan_of_finrank_le (finrank_ridgeSection_le P hP v j k hjk)
      have hsecs : (∑ i in (Finset.univ.erase j).erase k, facetSign P hP v i •
          sweep v w (hS (insert (ridgePoint P hP v j k)
            ((((Finset.univ.erase i).erase j).erase k).image P)))) ∈ LSpan m (m - 1) := by
        refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
        obtain ⟨hij, hik⟩ := SimplexCut.ne_ne_of_mem_erase_erase hi
        have hm2 := SimplexCut.two_le_of_three_ne hij hik hjk
        have e : m - 1 = m - 2 + 1 := by omega
        rw [e]
        exact sweep_hS_mem_LSpan hvw (Finset.insert_nonempty _ _)
          (finrank_ridgeSection_facet_le P hP v j k hij hik hjk)
      have hdec : (fun y => hS (Finset.univ.image P) y -
          ∑ l, facetSign P hP v l * sweep v w (hS ((Finset.univ.erase l).image P)) y) =
          (fun y => hS (Finset.univ.image (Function.update P k (ridgePoint P hP v j k))) y -
            ∑ l, facetSign (Function.update P k (ridgePoint P hP v j k)) h1 v l *
              sweep v w (hS ((Finset.univ.erase l).image
                (Function.update P k (ridgePoint P hP v j k)))) y) +
          (fun y => hS (Finset.univ.image (Function.update P j (ridgePoint P hP v j k))) y -
            ∑ l, facetSign (Function.update P j (ridgePoint P hP v j k)) h2 v l *
              sweep v w (hS ((Finset.univ.erase l).image
                (Function.update P j (ridgePoint P hP v j k)))) y) -
          hS (insert (ridgePoint P hP v j k) (((Finset.univ.erase j).erase k).image P)) +
          ∑ i in (Finset.univ.erase j).erase k, facetSign P hP v i •
            sweep v w (hS (insert (ridgePoint P hP v j k)
              ((((Finset.univ.erase i).erase j).erase k).image P))) := by
        funext y
        rw [residual_ridgeCut P hP v j k w hjk hsame h1 h2 y]
        simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hdec]
      exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ hR1 hR2) hsec) hsecs
    · -- at most one upper and one lower facet: a column
      push_neg at hpair
      obtain ⟨a, ha⟩ := exists_baryLin_neg P hP hv0
      obtain ⟨b, hb⟩ := exists_baryLin_pos P hP hv0
      have h0 : ∀ i, i ≠ a → i ≠ b → baryLin P hP v i = 0 := by
        intro i hia hib
        rcases lt_trichotomy (baryLin P hP v i) 0 with h | h | h
        · have := hpair i a hia
          nlinarith
        · exact h
        · have := hpair i b hib
          nlinarith
      exact residual_mem_LSpan_of_column P hP hvw ha hb h0

end

end MaxNN.ParamidGeom
