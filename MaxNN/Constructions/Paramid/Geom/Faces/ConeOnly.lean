import MaxNN.Constructions.Paramid.Geom.Faces.ConeOnly.LocalIdentity

/-!
# Theorem F: corrections by proper cone faces only

Module L8 of `work/depth2_simplex/smallest/PLAN_SMALLEST_GENERAL_N_2026-10-14.md` (Section 4.3,
Theorem F; S4 Theorem F; target statement in Section 8.1, Group B).  Helpers one level below:
`Faces/ConeOnly/SimplexGerm.lean` (germ differences of the faces of `Δ^n`) and
`Faces/ConeOnly/LocalIdentity.lean` (the local identity at a face of `Δ^n`).

Data: paramid cones `Q_j = coneVertsOn (γ j) (V j)`, `j ∈ s`, each of full dimension `n`, with
weights `a j`, and hypothesis (H): `∑_j a_j paramidOn (γ j) (V j) − h_{Δ^n} ∈ LSpan n (n − 1)`
(the class identity `∑_j a_j [Q_j] = [Δ^n]`).

* `hS_mem_of_subset_simplexVerts`: every proper face of `Δ^n` (a nonempty set `S ≠ Δ^n` of
  vertices) has its support function in the span of the proper cone-family members plus the
  linear forms.  Strong induction on `S` (`Finset.strongInduction`): a single vertex is a linear
  form; for `|S| ≥ 2` the local identity `hS_mem_of_ne_simplexVerts` expresses `hS S` through
  proper cone-family members, proper subsets of `S` (induction hypothesis) and linear forms.
* `simplex_sub_mem_coneFaceSpan` (**Theorem F**): `h_{Δ^n} − ∑_j a_j paramidOn (γ j) (V j)` is a
  combination of support functions of members `F ≠ Q_j` of the cone families
  `coneFamily (γ j) (V j)` (proper cone faces, base faces, apices), plus a linear form.  No face
  of `Δ^n` occurs.  Proof: the local identity for `S = Δ^n` (the Face Lemma relative to the whole
  space) writes `∑_j a_j paramidOn (γ j) (V j) − h_{Δ^n}` with proper cone-family members, proper
  faces of `Δ^n` and linear forms; the proper faces of `Δ^n` are then replaced by the previous
  item.
-/

namespace MaxNN.ParamidGeom.Faces

open BigOperators FiniteDimensional

noncomputable section

variable {n : ℕ} {ι : Type*}

/-- **The proper faces of `Δ^n` are spanned by proper cone faces.**  Under (H), for every
nonempty set `S ≠ Δ^n` of vertices of `Δ^n`, `hS S` is a combination of support functions of
proper cone-family members plus a linear form. -/
theorem hS_mem_of_subset_simplexVerts (hn : 1 ≤ n) {s : Finset ι} (a : ι → ℝ)
    {γ : ι → Fin n → ℝ} {V : ι → Finset (Fin n → ℝ)}
    (hfull : ∀ j ∈ s,
      finrank ℝ (vectorSpan ℝ (coneVertsOn (γ j) (V j) : Set (Fin n → ℝ))) = n)
    (hH : coneSum s a γ V - hS (simplexVerts n) ∈ LSpan n (n - 1)) :
    ∀ S : Finset (Fin n → ℝ), S ⊆ simplexVerts n → S.Nonempty → S ≠ simplexVerts n →
      hS S ∈ FSpan (properConeFamily s γ V) ⊔ LSpan n 0 := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hSΔ hSne hSΔ'
    by_cases h1 : S.card ≤ 1
    · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp (le_antisymm h1 (Finset.card_pos.mpr hSne))
      rw [GermAux.hS_singleton]
      exact Submodule.mem_sup_right (FlagAux.dot_mem_LSpan p 0)
    · have hloc := hS_mem_of_ne_simplexVerts hn a hfull hH hSΔ (by omega) hSΔ'
      have hle : properSubsetSpan S ≤ FSpan (properConeFamily s γ V) ⊔ LSpan n 0 := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨T, hTS, hTne, rfl⟩
        have hTS' := Finset.ssubset_iff_subset_ne.mp hTS
        refine ih T hTS (hTS'.1.trans hSΔ) hTne fun hTΔ => hTS'.2 ?_
        rw [hTΔ] at hTS' ⊢
        exact Finset.Subset.antisymm hTS'.1 hSΔ
      exact sup_le (sup_le le_sup_left hle) le_sup_right hloc

/-- **Theorem F** (PLAN Section 4.3; S4 Theorem F).  Let `Q_j = coneVertsOn (γ j) (V j)`,
`j ∈ s`, be full-dimensional paramid cones in `ℝ^n` (`n ≥ 2`) with weights `a j` such that
`∑_j a_j paramidOn (γ j) (V j) − h_{Δ^n} ∈ LSpan n (n − 1)`.  Then
`h_{Δ^n} − ∑_j a_j paramidOn (γ j) (V j)` is a combination of support functions of the members
`F ≠ Q_j` of the cone families `coneFamily (γ j) (V j)`, plus a linear form: the corrections
need proper cone faces only, no face of `Δ^n`. -/
theorem simplex_sub_mem_coneFaceSpan {n : ℕ} (hn : 2 ≤ n) {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (γ : ι → Fin n → ℝ) (V : ι → Finset (Fin n → ℝ))
    (hfull : ∀ j ∈ s, FiniteDimensional.finrank ℝ
      (vectorSpan ℝ (coneVertsOn (γ j) (V j) : Set (Fin n → ℝ))) = n)
    (hH : (fun y => ∑ j in s, a j * paramidOn (γ j) (V j) y - hS (simplexVerts n) y) ∈
      LSpan n (n - 1)) :
    (fun y => hS (simplexVerts n) y - ∑ j in s, a j * paramidOn (γ j) (V j) y) ∈
      Submodule.span ℝ {f | ∃ j ∈ s, ∃ F ∈ coneFamily (γ j) (V j),
        F ≠ coneVertsOn (γ j) (V j) ∧ F.Nonempty ∧ f = hS F} ⊔ LSpan n 0 := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hH' : coneSum s a γ V - hS (simplexVerts n) ∈ LSpan n (n - 1) := hH
  -- the local identity for `S = Δ^n` (empty list of directions)
  have htop := iterGermDiff_coneSum_sub_mem a hfull hH' (Finset.Subset.refl (simplexVerts n))
    (by rw [card_simplexVerts]; omega) List.nodup_nil
    (by rw [List.toFinset_nil, Finset.sdiff_self])
  rw [List.map_nil, iterGermDiff_nil, List.length_nil, pow_zero, one_smul] at htop
  -- the proper faces of `Δ^n` are spanned by proper cone-family members and linear forms
  have hle : properSubsetSpan (simplexVerts n) ≤
      FSpan (properConeFamily s γ V) ⊔ LSpan n 0 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨T, hTΔ, hTne, rfl⟩
    have hTΔ' := Finset.ssubset_iff_subset_ne.mp hTΔ
    exact hS_mem_of_subset_simplexVerts hn1 a hfull hH' T hTΔ'.1 hTne hTΔ'.2
  have h2 : coneSum s a γ V - hS (simplexVerts n) ∈
      FSpan (properConeFamily s γ V) ⊔ LSpan n 0 :=
    sup_le (sup_le le_sup_left hle) le_sup_right htop
  -- the proper cone-family members are the generators of the target span
  have h3 : FSpan (properConeFamily s γ V) ≤
      Submodule.span ℝ {f | ∃ j ∈ s, ∃ F ∈ coneFamily (γ j) (V j),
        F ≠ coneVertsOn (γ j) (V j) ∧ F.Nonempty ∧ f = hS F} := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, ⟨j, hj, hF, hFQ⟩, hFne, rfl⟩
    exact Submodule.subset_span ⟨j, hj, F, hF, hFQ, hFne, rfl⟩
  have e : (fun y => hS (simplexVerts n) y - ∑ j in s, a j * paramidOn (γ j) (V j) y) =
      -(coneSum s a γ V - hS (simplexVerts n)) := by
    funext y
    simp only [coneSum, Pi.neg_apply, Pi.sub_apply, neg_sub]
  rw [e]
  exact sup_le_sup_right h3 _ (Submodule.neg_mem _ h2)

end

end MaxNN.ParamidGeom.Faces
