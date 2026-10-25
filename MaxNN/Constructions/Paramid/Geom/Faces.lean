import MaxNN.Constructions.Paramid.Geom.Faces.Defs
import MaxNN.Constructions.Paramid.Geom.Faces.Peel
import MaxNN.Constructions.Paramid.Geom.Faces.Annihilate

/-!
# The Face Lemma relative to a subspace

Module L6 of `work/depth2_simplex/smallest/PLAN_SMALLEST_GENERAL_N_2026-10-14.md` (Section 4.3,
Face Lemma; target statements in Section 8.1, Group B). The finite elimination
proof is in `Geom/Faces/Annihilate.lean`; `Geom/Faces/Peel.lean` remains imported
for compatibility with its existing consumers.

* `LSpan_zero_eq`: the support functions of point sets of affine dimension `0` span exactly the
  linear forms, `LSpan m 0 = span {⟨p, ·⟩}`.
* `face_lemma_rel`: **Face Lemma relative to `U`.**  Let `𝔉` be face-closed, `dim U ≥ 1`, and let
  `f` be a combination of support functions of members of `𝔉` that lies in `LSpan m (dim U − 1)`.
  Then `f` is a combination of support functions `hS (face u F)`, `F ∈ 𝔉`, in directions `u` that
  do not annihilate `U` (`GSpanRel 𝔉 U`), plus a linear form (`LSpan m 0`).
* `face_lemma_rel_proper`: the second sentence of the Face Lemma of Section 4.3.  A face of any
  point set in a direction that does not annihilate `U` has a direction space not containing `U`
  (`not_le_vectorSpan_face`), so the generators are support functions of members `F ∈ 𝔉` with
  `U ⊄ dir F`.  In particular no generator is `hS G` for a member `G` with `U ≤ dir G`
  (`face_ne_of_le_vectorSpan`): if the top members are parallel to `U`, the generators are support
  functions of their proper faces.
* `face_lemma_top`: the case `U = ℝ^m` (the Face Lemma in span form, all nonzero directions).

*Proof of `face_lemma_rel`* (`mem_GSpanRel_of_lt_finrank`). Write `g` as a finite
lower-dimensional support-function sum. For each summand choose a direction
orthogonal to its direction space but not to `U`, and subtract the current germ.
This kills the summand and every subset support function produced from it by
earlier operations. The final residual is zero, and every subtracted germ lies
in `GSpanRel 𝔉 U`. The historical theorem with an added linear remainder follows
immediately; simultaneous generic directions and dimension induction are unnecessary.
-/

namespace MaxNN.ParamidGeom.Faces

open BigOperators FiniteDimensional

variable {m : ℕ} {𝔉 : Set (Finset (Fin m → ℝ))} {f : (Fin m → ℝ) → ℝ}

/-! ## The zero-dimensional span -/

/-- A point set of affine dimension `0` containing `p` is `{p}`. -/
theorem eq_singleton_of_finrank_vectorSpan_le_zero {S : Finset (Fin m → ℝ)} {p : Fin m → ℝ}
    (hp : p ∈ S) (hdim : finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) ≤ 0) : S = {p} := by
  have hbot : vectorSpan ℝ (S : Set (Fin m → ℝ)) = ⊥ :=
    Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hdim)
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hp, fun q hq => ?_⟩
  have hmem : q -ᵥ p ∈ vectorSpan ℝ (S : Set (Fin m → ℝ)) :=
    vsub_mem_vectorSpan ℝ (Finset.mem_coe.mpr hq) (Finset.mem_coe.mpr hp)
  rw [hbot, Submodule.mem_bot, vsub_eq_sub, sub_eq_zero] at hmem
  exact hmem

/-- **The zero-dimensional span is the space of linear forms**: the support functions of point
sets of affine dimension `0` (single points) span exactly the linear forms `⟨p, ·⟩`. -/
theorem LSpan_zero_eq : LSpan m 0 = Submodule.span ℝ (Set.range fun p : Fin m → ℝ => dot p) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr fun g hg => ?_
    obtain ⟨S, ⟨p, hp⟩, hdim, rfl⟩ := Sweep.eq_hS_of_mem_lowerDimSupport hg
    rw [eq_singleton_of_finrank_vectorSpan_le_zero hp hdim, Sweep.hS_singleton]
    exact Submodule.subset_span ⟨p, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact FlagAux.dot_mem_LSpan p 0

/-! ## The Face Lemma relative to a subspace -/

/-- Compatibility form of finite face elimination: for `d < dim U`, every
function of `FSpan 𝔉 ∩ LSpan m d` lies in `GSpanRel 𝔉 U ⊔ LSpan m 0`. -/
theorem mem_GSpanRel_sup_of_lt_finrank (U : Submodule ℝ (Fin m → ℝ)) (h𝔉 : FaceClosed 𝔉)
    {d : ℕ} (hd : d < finrank ℝ U) {g : (Fin m → ℝ) → ℝ} (hgF : g ∈ FSpan 𝔉)
    (hgL : g ∈ LSpan m d) : g ∈ GSpanRel 𝔉 U ⊔ LSpan m 0 :=
  Submodule.mem_sup_left (mem_GSpanRel_of_lt_finrank U h𝔉 hd hgF hgL)

/-- **Face Lemma relative to a subspace.**  Let `𝔉` be face-closed and `dim U ≥ 1`.  A
combination `f` of support functions of members of `𝔉` that lies in `LSpan m (dim U − 1)` is a
combination of support functions `hS (face u F)`, `F ∈ 𝔉`, in directions `u` that do not
annihilate `U`, plus a linear form. -/
theorem face_lemma_rel (U : Submodule ℝ (Fin m → ℝ)) (hU : 1 ≤ FiniteDimensional.finrank ℝ U)
    (h𝔉 : FaceClosed 𝔉) (hf : f ∈ FSpan 𝔉)
    (hlow : f ∈ LSpan m (FiniteDimensional.finrank ℝ U - 1)) : f ∈ GSpanRel 𝔉 U ⊔ LSpan m 0 :=
  mem_GSpanRel_sup_of_lt_finrank U h𝔉 (Nat.sub_lt hU Nat.one_pos) hf hlow

/-- **Face Lemma** (`U = ℝ^m`).  For `m ≥ 1`, a combination of support functions of members of a
face-closed family that lies in `LSpan m (m − 1)` is a combination of support functions of faces
of members in nonzero directions (`exists_mem_top_dot_ne_zero_iff`), plus a linear form. -/
theorem face_lemma_top (hm : 1 ≤ m) (h𝔉 : FaceClosed 𝔉) (hf : f ∈ FSpan 𝔉)
    (hlow : f ∈ LSpan m (m - 1)) : f ∈ GSpanRel 𝔉 ⊤ ⊔ LSpan m 0 := by
  have hrank : finrank ℝ (⊤ : Submodule ℝ (Fin m → ℝ)) = m := by simp
  have hU : 1 ≤ finrank ℝ (⊤ : Submodule ℝ (Fin m → ℝ)) := by
    rw [hrank]
    exact hm
  have hlow' : f ∈ LSpan m (finrank ℝ (⊤ : Submodule ℝ (Fin m → ℝ)) - 1) := by
    rw [hrank]
    exact hlow
  exact face_lemma_rel ⊤ hU h𝔉 hf hlow'

/-! ## The generators are proper faces -/

/-- In a direction `u` that does not annihilate `U`, the direction space of the face `face u F`
does not contain `U` (it is orthogonal to `u`). -/
theorem not_le_vectorSpan_face {U : Submodule ℝ (Fin m → ℝ)} {u : Fin m → ℝ}
    (hu : ∃ w ∈ U, dot u w ≠ 0) (F : Finset (Fin m → ℝ)) :
    ¬ U ≤ vectorSpan ℝ (face u F : Set (Fin m → ℝ)) := by
  intro hle
  obtain ⟨w, hw, hdot⟩ := hu
  have h := FlagAux.vectorSpan_face_le_ker u F (hle hw)
  rw [LinearMap.mem_ker, SupportCut.dotL_apply] at h
  exact hdot h

/-- In a direction that does not annihilate `U`, no face of a point set is a point set `G` whose
direction space contains `U`. -/
theorem face_ne_of_le_vectorSpan {U : Submodule ℝ (Fin m → ℝ)} {u : Fin m → ℝ}
    (hu : ∃ w ∈ U, dot u w ≠ 0) (F : Finset (Fin m → ℝ)) {G : Finset (Fin m → ℝ)}
    (hU : U ≤ vectorSpan ℝ (G : Set (Fin m → ℝ))) : face u F ≠ G := by
  intro h
  apply not_le_vectorSpan_face hu F
  rw [h]
  exact hU

/-- For a face-closed family, the face generators relative to `U` are support functions of
nonempty members whose direction space does not contain `U`. -/
theorem GSpanRel_le_span_not_le (h𝔉 : FaceClosed 𝔉) (U : Submodule ℝ (Fin m → ℝ)) :
    GSpanRel 𝔉 U ≤ Submodule.span ℝ {g | ∃ F ∈ 𝔉, F.Nonempty ∧
      ¬ U ≤ vectorSpan ℝ (F : Set (Fin m → ℝ)) ∧ g = hS F} := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨F, hF, hne, u, hu, rfl⟩
  exact Submodule.subset_span
    ⟨face u F, h𝔉 F hF u, face_nonempty hne u, not_le_vectorSpan_face hu F, rfl⟩

/-- **Face Lemma relative to a subspace, proper form.**  Under the hypotheses of
`face_lemma_rel`, `f` is a combination of support functions of nonempty members `F ∈ 𝔉` whose
direction space does not contain `U`, plus a linear form.  In particular no such `F` is a point
set `G` with `U ≤ dir G`, e.g. a top-dimensional member parallel to `U`. -/
theorem face_lemma_rel_proper (U : Submodule ℝ (Fin m → ℝ)) (hU : 1 ≤ finrank ℝ U)
    (h𝔉 : FaceClosed 𝔉) (hf : f ∈ FSpan 𝔉) (hlow : f ∈ LSpan m (finrank ℝ U - 1)) :
    f ∈ Submodule.span ℝ {g | ∃ F ∈ 𝔉, F.Nonempty ∧
      ¬ U ≤ vectorSpan ℝ (F : Set (Fin m → ℝ)) ∧ g = hS F} ⊔ LSpan m 0 :=
  sup_le_sup_right (GSpanRel_le_span_not_le h𝔉 U) _ (face_lemma_rel U hU h𝔉 hf hlow)

end MaxNN.ParamidGeom.Faces
