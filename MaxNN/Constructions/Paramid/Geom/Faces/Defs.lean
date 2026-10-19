import MaxNN.Constructions.Paramid.Geom.Germ

/-!
# Face-closed families and the spans of their support functions

Shared vocabulary of `Geom/Faces/*` (module L5 of
`work/depth2_simplex/smallest/PLAN_SMALLEST_GENERAL_N_2026-10-14.md`, Section 8.1, Group B).
A *family* is a set `𝔉` of finite point sets of `ℝ^m`.

* `FaceClosed 𝔉`: `𝔉` contains every face `face u F` of each of its members `F`.
* `FSpan 𝔉`: the real span of the support functions `hS F` of the nonempty members `F ∈ 𝔉`.
* `GSpanRel 𝔉 U`: the real span of the support functions `hS (face u F)` of the faces of nonempty
  members `F ∈ 𝔉` in the directions `u` that do not annihilate the subspace `U`, i.e.
  `⟨u, w⟩ ≠ 0` for some `w ∈ U`.  For `U = ⊤` these are the faces in nonzero directions.

Basic API: the generators are members (`hS_mem_FSpan`, `hS_face_mem_GSpanRel`),
`FSpan 𝔉 ≤ SSpan m`, monotonicity (`FSpan_mono`, `GSpanRel_mono`), the admissible directions for
`U = ⊤` are the nonzero ones (`exists_mem_top_dot_ne_zero_iff`), unions of face-closed families
are face-closed (`FaceClosed.union`, `faceClosed_iUnion`), and the closure properties used by the
relative Face Lemma: the germ of a function of `FSpan 𝔉` in a direction `u` that does not
annihilate `U` lies in `GSpanRel 𝔉 U` (`germ_mem_GSpanRel`, and for finite sums of such germs
`sum_germ_mem_GSpanRel`); if `𝔉` is face-closed, `GSpanRel 𝔉 U ≤ FSpan 𝔉` and every germ of a
function of `FSpan 𝔉` lies in `FSpan 𝔉` (`germ_mem_FSpan`).
-/

namespace MaxNN.ParamidGeom.Faces

open BigOperators

/-- A family of finite point sets is *face-closed* if it contains every face of each member. -/
def FaceClosed {m : ℕ} (𝔉 : Set (Finset (Fin m → ℝ))) : Prop := ∀ F ∈ 𝔉, ∀ u, face u F ∈ 𝔉

/-- The real span of the support functions of the nonempty members of `𝔉`. -/
def FSpan {m : ℕ} (𝔉 : Set (Finset (Fin m → ℝ))) : Submodule ℝ ((Fin m → ℝ) → ℝ) :=
  Submodule.span ℝ {f | ∃ F ∈ 𝔉, F.Nonempty ∧ f = hS F}

/-- The real span of the support functions `hS (face u F)` of the faces of nonempty members
`F ∈ 𝔉` in the directions `u` that do not annihilate `U` (`⟨u, w⟩ ≠ 0` for some `w ∈ U`). -/
def GSpanRel {m : ℕ} (𝔉 : Set (Finset (Fin m → ℝ))) (U : Submodule ℝ (Fin m → ℝ)) :
    Submodule ℝ ((Fin m → ℝ) → ℝ) :=
  Submodule.span ℝ {f | ∃ F ∈ 𝔉, F.Nonempty ∧ ∃ u, (∃ w ∈ U, dot u w ≠ 0) ∧ f = hS (face u F)}

variable {m : ℕ} {𝔉 : Set (Finset (Fin m → ℝ))}

/-! ## Generators -/

theorem hS_mem_FSpan {F : Finset (Fin m → ℝ)} (hF : F ∈ 𝔉) (hne : F.Nonempty) :
    hS F ∈ FSpan 𝔉 :=
  Submodule.subset_span ⟨F, hF, hne, rfl⟩

theorem hS_face_mem_GSpanRel (U : Submodule ℝ (Fin m → ℝ)) {F : Finset (Fin m → ℝ)}
    (hF : F ∈ 𝔉) (hne : F.Nonempty) {u : Fin m → ℝ} (hu : ∃ w ∈ U, dot u w ≠ 0) :
    hS (face u F) ∈ GSpanRel 𝔉 U :=
  Submodule.subset_span ⟨F, hF, hne, u, hu, rfl⟩

/-- Functions of `FSpan 𝔉` are combinations of support functions. -/
theorem FSpan_le_SSpan (𝔉 : Set (Finset (Fin m → ℝ))) : FSpan 𝔉 ≤ SSpan m := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨F, -, hne, rfl⟩
  exact GermAux.hS_mem_SSpan hne

/-- For a face-closed family, the face generators are generators of `FSpan 𝔉`. -/
theorem GSpanRel_le_FSpan (h𝔉 : FaceClosed 𝔉) (U : Submodule ℝ (Fin m → ℝ)) :
    GSpanRel 𝔉 U ≤ FSpan 𝔉 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨F, hF, hne, u, -, rfl⟩
  exact hS_mem_FSpan (h𝔉 F hF u) (face_nonempty hne u)

theorem FSpan_mono {𝔉₁ 𝔉₂ : Set (Finset (Fin m → ℝ))} (h : 𝔉₁ ⊆ 𝔉₂) :
    FSpan 𝔉₁ ≤ FSpan 𝔉₂ :=
  Submodule.span_mono fun _ ⟨F, hF, hne, hf⟩ => ⟨F, h hF, hne, hf⟩

/-- `GSpanRel 𝔉 U` grows with the family and with the subspace. -/
theorem GSpanRel_mono {𝔉₁ 𝔉₂ : Set (Finset (Fin m → ℝ))} (h : 𝔉₁ ⊆ 𝔉₂)
    {U₁ U₂ : Submodule ℝ (Fin m → ℝ)} (hU : U₁ ≤ U₂) : GSpanRel 𝔉₁ U₁ ≤ GSpanRel 𝔉₂ U₂ :=
  Submodule.span_mono fun _ ⟨F, hF, hne, u, ⟨w, hw, hdot⟩, hf⟩ =>
    ⟨F, h hF, hne, u, ⟨w, hU hw, hdot⟩, hf⟩

/-- Relative to `U = ⊤`, the admissible directions are the nonzero ones. -/
theorem exists_mem_top_dot_ne_zero_iff {u : Fin m → ℝ} :
    (∃ w ∈ (⊤ : Submodule ℝ (Fin m → ℝ)), dot u w ≠ 0) ↔ u ≠ 0 := by
  constructor
  · rintro ⟨w, -, hw⟩ rfl
    apply hw
    rw [← zero_smul ℝ (0 : Fin m → ℝ), SupportCut.dot_smul_left, zero_mul]
  · intro hu
    exact ⟨u, Submodule.mem_top, fun h => hu (SupportCut.eq_zero_of_dot_self_eq_zero h)⟩

/-! ## Unions of face-closed families -/

theorem FaceClosed.union {𝔉₁ 𝔉₂ : Set (Finset (Fin m → ℝ))} (h₁ : FaceClosed 𝔉₁)
    (h₂ : FaceClosed 𝔉₂) : FaceClosed (𝔉₁ ∪ 𝔉₂) := by
  rintro F (hF | hF) u
  · exact Or.inl (h₁ F hF u)
  · exact Or.inr (h₂ F hF u)

/-- A union of face-closed families is face-closed (also for `⋃ j ∈ s, 𝔉 j`, applying this
twice). -/
theorem faceClosed_iUnion {ι : Sort*} {𝔉 : ι → Set (Finset (Fin m → ℝ))}
    (h : ∀ i, FaceClosed (𝔉 i)) : FaceClosed (⋃ i, 𝔉 i) := by
  intro F hF u
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hF
  exact Set.mem_iUnion.mpr ⟨i, h i F hi u⟩

/-! ## Germs -/

/-- In a direction `u` that does not annihilate `U`, a function of `FSpan 𝔉` has a germ in
`GSpanRel 𝔉 U`. -/
theorem exists_isGerm_mem_GSpanRel (U : Submodule ℝ (Fin m → ℝ)) {g : (Fin m → ℝ) → ℝ}
    (hg : g ∈ FSpan 𝔉) {u : Fin m → ℝ} (hu : ∃ w ∈ U, dot u w ≠ 0) :
    ∃ h ∈ GSpanRel 𝔉 U, IsGerm g u h := by
  refine Submodule.span_induction
    (p := fun g => ∃ h ∈ GSpanRel 𝔉 U, IsGerm g u h) hg ?_ ?_ ?_ ?_
  · rintro _ ⟨F, hF, hne, rfl⟩
    exact ⟨hS (face u F), hS_face_mem_GSpanRel U hF hne hu, isGerm_hS hne u⟩
  · exact ⟨0, Submodule.zero_mem _, isGerm_zero u⟩
  · rintro g₁ g₂ ⟨h₁, hh₁, H₁⟩ ⟨h₂, hh₂, H₂⟩
    exact ⟨h₁ + h₂, Submodule.add_mem _ hh₁ hh₂, H₁.add H₂⟩
  · rintro c g ⟨h, hh, H⟩
    exact ⟨c • h, Submodule.smul_mem _ c hh, H.smul c⟩

/-- **Germs land in the face span.**  In a direction `u` that does not annihilate `U`, the germ
of a function of `FSpan 𝔉` lies in `GSpanRel 𝔉 U`. -/
theorem germ_mem_GSpanRel (U : Submodule ℝ (Fin m → ℝ)) {g : (Fin m → ℝ) → ℝ}
    (hg : g ∈ FSpan 𝔉) {u : Fin m → ℝ} (hu : ∃ w ∈ U, dot u w ≠ 0) :
    germ g u ∈ GSpanRel 𝔉 U := by
  obtain ⟨h, hh, H⟩ := exists_isGerm_mem_GSpanRel U hg hu
  rw [germ_eq_of_isGerm H]
  exact hh

/-- A finite sum of germs in directions that do not annihilate `U` lies in `GSpanRel 𝔉 U`. -/
theorem sum_germ_mem_GSpanRel (U : Submodule ℝ (Fin m → ℝ)) {g : (Fin m → ℝ) → ℝ}
    (hg : g ∈ FSpan 𝔉) {E : Finset (Fin m → ℝ)} (hE : ∀ e ∈ E, ∃ w ∈ U, dot e w ≠ 0) :
    (fun y => ∑ e in E, germ g e y) ∈ GSpanRel 𝔉 U := by
  have h : (fun y => ∑ e in E, germ g e y) = ∑ e in E, germ g e := by
    funext y
    rw [Finset.sum_apply]
  rw [h]
  exact Submodule.sum_mem _ fun e he => germ_mem_GSpanRel U hg (hE e he)

/-- **Face-closed families are germ-closed.**  If `𝔉` is face-closed, every germ of a function
of `FSpan 𝔉` lies in `FSpan 𝔉`. -/
theorem germ_mem_FSpan (h𝔉 : FaceClosed 𝔉) {g : (Fin m → ℝ) → ℝ} (hg : g ∈ FSpan 𝔉)
    (u : Fin m → ℝ) : germ g u ∈ FSpan 𝔉 := by
  have key : ∃ h ∈ FSpan 𝔉, IsGerm g u h := by
    refine Submodule.span_induction
      (p := fun g => ∃ h ∈ FSpan 𝔉, IsGerm g u h) hg ?_ ?_ ?_ ?_
    · rintro _ ⟨F, hF, hne, rfl⟩
      exact ⟨hS (face u F), hS_mem_FSpan (h𝔉 F hF u) (face_nonempty hne u), isGerm_hS hne u⟩
    · exact ⟨0, Submodule.zero_mem _, isGerm_zero u⟩
    · rintro g₁ g₂ ⟨h₁, hh₁, H₁⟩ ⟨h₂, hh₂, H₂⟩
      exact ⟨h₁ + h₂, Submodule.add_mem _ hh₁ hh₂, H₁.add H₂⟩
    · rintro c g ⟨h, hh, H⟩
      exact ⟨c • h, Submodule.smul_mem _ c hh, H.smul c⟩
  obtain ⟨h, hh, H⟩ := key
  rw [germ_eq_of_isGerm H]
  exact hh

end MaxNN.ParamidGeom.Faces
