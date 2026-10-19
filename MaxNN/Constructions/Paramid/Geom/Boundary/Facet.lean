import MaxNN.Constructions.Paramid.Geom.Boundary.ConeFaces
import MaxNN.Constructions.Paramid.Geom.Boundary.Sign
import MaxNN.Constructions.Paramid.Geom.Flag
import MaxNN.Constructions.Paramid.Geom.UnitGerm

/-!
# Facet data of a paramid unit modulo lower dimension

Helper of `Geom/Boundary.lean` (module `M-Boundary` of
`work/depth2_simplex/lean_core/BLUEPRINT.md`).  For a paramid unit `paramidOn γ V` and a direction
`u`, write `Z = {v ∈ V | ⟨v, u⟩ = 0}` (the labels orthogonal to `u`).

* `unitGerm_pos_mem_LSpan_card`: if `A = ⟨γ, u⟩ + ∑_{v ∈ V} relu ⟨v, u⟩ > 0`, the germ (the support
  function of a face of the base parallelepiped) lies in `LSpan m |Z|`.
* **Two labels crossing `u^⊥`** (`germDiff_paramidOn_mem_LSpan_of_two`): the facet datum lies in
  `LSpan m (|V| − 1)`.
* **One label `v₀` crossing `u^⊥`** (`germDiff_paramidOn_single_sub_mem_LSpan`): modulo
  `LSpan m (|V| − 1)` the facet datum is
  `sgn ⟨v₀, u⟩ · ([⟨γ + v₀, u⟩ = 0] · paramidOn (γ + v₀) (V ∖ v₀)`
  `− [⟨γ, u⟩ = 0] · paramidOn γ (V ∖ v₀))`
  — the two lateral facets through `v₀`, i.e. the two boundary terms of `d [γ; L]` at `v₀`.
* **No label crossing `u^⊥`** (`germDiff_paramidOn_mem_LSpan_one_of_forall_orth`): if moreover
  `⟨γ, u⟩ ≠ 0`, the facet datum is the base parallelepiped up to sign, in `LSpan m 1`.
* Flag functionals of length one of segments: `flagFun_singleton_relu_dot`
  (`Λ_{[w]} (relu ⟨x, ·⟩) = |⟨x, w⟩|`) and `flagFun_singleton_dot_add_relu_dot`.
-/

namespace MaxNN.ParamidGeom

open BigOperators FiniteDimensional BoundaryAux

variable {m : ℕ}

/-- `0 < A`: the germ of a paramid unit lies in `LSpan m |Z|`. -/
theorem unitGerm_pos_mem_LSpan_card {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)} {u : Fin m → ℝ}
    (hA : 0 < dot γ u + ∑ v in V, relu (dot v u)) :
    unitGerm γ V u ∈ LSpan m (V.filter (fun v => dot v u = 0)).card := by
  rw [unitGerm_eq_hS_face]
  have hsum : ∑ v in V, relu (dot u v) = ∑ v in V, relu (dot v u) :=
    Finset.sum_congr rfl fun v _ => by rw [SupportCut.dot_comm]
  have hA' : 0 < dot u γ + ∑ v in V, relu (dot u v) := by
    rw [hsum, SupportCut.dot_comm]
    exact hA
  have hdim := finrank_vectorSpan_face_coneVertsOn_of_pos u γ V hA'
  have hZ : V.filter (fun v => dot u v = 0) = V.filter (fun v => dot v u = 0) :=
    Finset.filter_congr fun v _ => by rw [SupportCut.dot_comm]
  rw [hZ] at hdim
  exact FlagAux.hS_mem_LSpan (face_nonempty (DoublingAux.coneVertsOn_nonempty γ V) u) hdim

/-- **Two labels crossing `u^⊥`**: the facet datum is lower-dimensional. -/
theorem germDiff_paramidOn_mem_LSpan_of_two {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)}
    {u v₁ v₂ : Fin m → ℝ} (h₁ : v₁ ∈ V) (h₂ : v₂ ∈ V) (hne : v₁ ≠ v₂) (hb₁ : dot v₁ u ≠ 0)
    (hb₂ : dot v₂ u ≠ 0) {k : ℕ} (hk : V.card ≤ k + 1) :
    germDiff u (paramidOn γ V) ∈ LSpan m k := by
  rw [germDiff_paramidOn]
  have hsub : V.filter (fun v => dot v u = 0) ⊆ (V.erase v₁).erase v₂ := by
    intro v hv
    rw [Finset.mem_filter] at hv
    refine Finset.mem_erase.mpr ⟨fun e => hb₂ (e ▸ hv.2), Finset.mem_erase.mpr
      ⟨fun e => hb₁ (e ▸ hv.2), hv.1⟩⟩
  have hc := Finset.card_le_of_subset hsub
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, h₂⟩),
    Finset.card_erase_of_mem h₁] at hc
  have h2 : 2 ≤ V.card := by
    have := Finset.card_le_of_subset (show ({v₁, v₂} : Finset (Fin m → ℝ)) ⊆ V by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact h₁
      · rw [Finset.mem_singleton.mp hx]; exact h₂)
    rwa [Finset.card_doubleton hne] at this
  have hZ : (V.filter (fun v => dot v u = 0)).card + 1 ≤ k := by omega
  have hZ' : V.filter (fun v => dot v (-u) = 0) = V.filter (fun v => dot v u = 0) :=
    UnitGermAux.filter_dot_neg_eq_zero V u
  refine Submodule.sub_mem _ (DoublingAux.LSpan_mono hZ (unitGerm_mem_LSpan γ V u)) ?_
  have h := unitGerm_mem_LSpan γ V (-u)
  rw [hZ'] at h
  exact DoublingAux.LSpan_mono hZ h

/-- **One label crossing `u^⊥`, one side**: modulo `LSpan m |V ∖ v₀|` the germ in direction `u` is
the lateral facet through `γ + v₀` (if `⟨v₀, u⟩ > 0`) or through `γ` (if `⟨v₀, u⟩ < 0`), when it
is a face of the cone in direction `u` at all. -/
theorem unitGerm_single_sub_mem_LSpan {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)}
    {u v₀ : Fin m → ℝ} (hv₀ : v₀ ∈ V) (hb : dot v₀ u ≠ 0)
    (hrest : ∀ v ∈ V, v ≠ v₀ → dot v u = 0) :
    unitGerm γ V u - (if 0 < dot v₀ u then
        (if dot (γ + v₀) u = 0 then paramidOn (γ + v₀) (V.erase v₀) else 0)
      else (if dot γ u = 0 then paramidOn γ (V.erase v₀) else 0)) ∈
      LSpan m (V.erase v₀).card := by
  have hsum : ∑ v in V, relu (dot v u) = relu (dot v₀ u) := by
    refine Finset.sum_eq_single v₀ (fun v hv hne => ?_) (fun h => absurd hv₀ h)
    rw [hrest v hv hne]
    exact relu_of_nonpos le_rfl
  have hZ : V.filter (fun v => dot v u = 0) = V.erase v₀ := by
    ext v
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hv, hz⟩
      exact ⟨fun e => hb (e ▸ hz), hv⟩
    · rintro ⟨hne, hv⟩
      exact ⟨hv, hrest v hv hne⟩
  have hposcase : ∀ c : ℝ, dot γ u + ∑ v in V, relu (dot v u) = c → c ≠ 0 →
      unitGerm γ V u ∈ LSpan m (V.erase v₀).card := by
    intro c hc hc0
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · rw [unitGerm_of_neg (by rw [hc]; exact hneg)]
      exact Submodule.zero_mem _
    · have h := unitGerm_pos_mem_LSpan_card (γ := γ) (V := V) (u := u) (by rw [hc]; exact hpos)
      rwa [hZ] at h
  by_cases hpos : 0 < dot v₀ u
  · rw [if_pos hpos]
    have hA : dot γ u + ∑ v in V, relu (dot v u) = dot (γ + v₀) u := by
      rw [hsum, relu_of_nonneg hpos.le, SupportCut.dot_add_left]
    by_cases hc : dot (γ + v₀) u = 0
    · rw [if_pos hc, unitGerm_of_single_pos hv₀ hpos hrest
        (by rw [← SupportCut.dot_add_left]; exact hc), sub_self]
      exact Submodule.zero_mem _
    · rw [if_neg hc, sub_zero]
      exact hposcase _ hA hc
  · rw [if_neg hpos]
    have hneg : dot v₀ u < 0 := lt_of_le_of_ne (not_lt.mp hpos) hb
    have hA : dot γ u + ∑ v in V, relu (dot v u) = dot γ u := by
      rw [hsum, relu_of_nonpos hneg.le, add_zero]
    by_cases hc : dot γ u = 0
    · rw [if_pos hc, unitGerm_of_single_neg hneg hrest hc, sub_self]
      exact Submodule.zero_mem _
    · rw [if_neg hc, sub_zero]
      exact hposcase _ hA hc

/-- **One label crossing `u^⊥`**: modulo `LSpan m |V ∖ v₀|`, the facet datum of a paramid unit is
`sgn ⟨v₀, u⟩ · (lateral facet through γ + v₀ − lateral facet through γ)`, each facet counted when
it is orthogonal to `u`. -/
theorem germDiff_paramidOn_single_sub_mem_LSpan {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)}
    {u v₀ : Fin m → ℝ} (hv₀ : v₀ ∈ V) (hb : dot v₀ u ≠ 0)
    (hrest : ∀ v ∈ V, v ≠ v₀ → dot v u = 0) :
    germDiff u (paramidOn γ V) - sgn (dot v₀ u) •
      ((if dot (γ + v₀) u = 0 then paramidOn (γ + v₀) (V.erase v₀) else 0) -
        (if dot γ u = 0 then paramidOn γ (V.erase v₀) else 0)) ∈
      LSpan m (V.erase v₀).card := by
  rw [germDiff_paramidOn]
  have h1 := unitGerm_single_sub_mem_LSpan (γ := γ) hv₀ hb hrest
  have hb' : dot v₀ (-u) ≠ 0 := by
    rw [UnitGermAux.dot_neg_right]
    exact neg_ne_zero.mpr hb
  have hrest' : ∀ v ∈ V, v ≠ v₀ → dot v (-u) = 0 := fun v hv hne => by
    rw [UnitGermAux.dot_neg_right, hrest v hv hne, neg_zero]
  have h2 := unitGerm_single_sub_mem_LSpan (γ := γ) (u := -u) hv₀ hb' hrest'
  simp only [UnitGermAux.dot_neg_right, neg_pos, neg_eq_zero] at h2
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)] at h1
    rw [if_pos hneg] at h2
    rw [sgn_of_neg hneg, neg_one_smul]
    convert Submodule.sub_mem _ h1 h2 using 1
    abel
  · rw [if_pos hpos] at h1
    rw [if_neg (not_lt.mpr hpos.le)] at h2
    rw [sgn_of_pos hpos, one_smul]
    convert Submodule.sub_mem _ h1 h2 using 1
    abel

/-- **No label crossing `u^⊥`, apex off `u^⊥`**: the facet datum is `±` the base parallelepiped,
which lies in `LSpan m 1`. -/
theorem germDiff_paramidOn_mem_LSpan_one_of_forall_orth {γ : Fin m → ℝ}
    {V : Finset (Fin m → ℝ)} {u : Fin m → ℝ} (hV : ∀ v ∈ V, dot v u = 0) (hγ : dot γ u ≠ 0) :
    germDiff u (paramidOn γ V) ∈ LSpan m 1 := by
  rw [germDiff_paramidOn]
  have hsum : ∑ v in V, relu (dot v u) = 0 :=
    Finset.sum_eq_zero fun v hv => by rw [hV v hv]; exact relu_of_nonpos le_rfl
  have hsum' : ∑ v in V, relu (dot v (-u)) = 0 :=
    Finset.sum_eq_zero fun v hv => by
      rw [UnitGermAux.dot_neg_right, hV v hv, neg_zero]; exact relu_of_nonpos le_rfl
  rcases lt_or_gt_of_ne hγ with hneg | hpos
  · rw [unitGerm_of_neg (by rw [hsum, add_zero]; exact hneg), zero_sub]
    refine Submodule.neg_mem _ (unitGerm_pos_mem_LSpan ?_)
    rw [hsum', add_zero, UnitGermAux.dot_neg_right]
    linarith
  · rw [unitGerm_of_neg (u := -u) (by rw [hsum', add_zero, UnitGermAux.dot_neg_right]; linarith),
      sub_zero]
    exact unitGerm_pos_mem_LSpan (by rw [hsum, add_zero]; exact hpos)

/-- **No label crossing `u^⊥`, apex off `u^⊥`, exactly**: the facet datum is
`sgn ⟨γ, u⟩ · (⟨γ, ·⟩ + ∑_{v ∈ V} relu ⟨v, ·⟩)`, the base parallelepiped with its sign. -/
theorem germDiff_paramidOn_of_forall_orth_of_ne {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)}
    {u : Fin m → ℝ} (hV : ∀ v ∈ V, dot v u = 0) (hγ : dot γ u ≠ 0) :
    germDiff u (paramidOn γ V) =
      sgn (dot γ u) • (fun y => dot γ y + ∑ v in V, relu (dot v y)) := by
  rw [germDiff_paramidOn]
  have hsum : ∑ v in V, relu (dot v u) = 0 :=
    Finset.sum_eq_zero fun v hv => by rw [hV v hv]; exact relu_of_nonpos le_rfl
  have hsum' : ∑ v in V, relu (dot v (-u)) = 0 :=
    Finset.sum_eq_zero fun v hv => by
      rw [UnitGermAux.dot_neg_right, hV v hv, neg_zero]; exact relu_of_nonpos le_rfl
  have hV' : ∀ v ∈ V, dot v (-u) = 0 := fun v hv => by
    rw [UnitGermAux.dot_neg_right, hV v hv, neg_zero]
  rcases lt_or_gt_of_ne hγ with hneg | hpos
  · rw [unitGerm_of_neg (by rw [hsum, add_zero]; exact hneg), zero_sub, sgn_of_neg hneg,
      neg_one_smul,
      unitGerm_of_forall_orth_of_pos hV' (by rw [UnitGermAux.dot_neg_right]; linarith)]
  · rw [unitGerm_of_neg (u := -u) (by rw [hsum', add_zero, UnitGermAux.dot_neg_right]; linarith),
      sub_zero, sgn_of_pos hpos, one_smul, unitGerm_of_forall_orth_of_pos hV hpos]

/-! ## Flag functionals of length one -/

namespace BoundaryAux

theorem relu_dot_mem_SSpan (x : Fin m → ℝ) : (fun y => relu (dot x y)) ∈ SSpan m := by
  have h := paramidOn_mem_SSpan x (∅ : Finset (Fin m → ℝ))
  have e : paramidOn x ∅ = fun y => relu (dot x y) := funext (UnitGermAux.paramidOn_empty x)
  rwa [e] at h

/-- A flag functional of a guarded function. -/
theorem flagFun_ite (us : List (Fin m → ℝ)) (c : Prop) [Decidable c] (f : (Fin m → ℝ) → ℝ) :
    flagFun us (if c then f else 0) = if c then flagFun us f else 0 := by
  split_ifs
  · rfl
  · exact flagFun_zero us

theorem ite_mem_SSpan (c : Prop) [Decidable c] {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) :
    (if c then f else 0) ∈ SSpan m := by
  split_ifs
  · exact hf
  · exact Submodule.zero_mem _

end BoundaryAux

/-- `Λ_{[w]} (relu ⟨x, ·⟩) = |⟨x, w⟩|`: the width of the segment `[0, x]` along `w`. -/
theorem flagFun_singleton_relu_dot (x w : Fin m → ℝ) :
    flagFun [w] (fun y => relu (dot x y)) = |dot x w| := by
  have e : (fun y => relu (dot x y)) = hS (coneVertsOn x ∅) := by
    rw [← paramidOn_eq_hS]
    funext y
    rw [UnitGermAux.paramidOn_empty]
  rw [e, flagFun_singleton_hS (DoublingAux.coneVertsOn_nonempty x ∅), ← paramidOn_eq_hS,
    UnitGermAux.paramidOn_empty, UnitGermAux.paramidOn_empty, UnitGermAux.dot_neg_right]
  rcases le_total 0 (dot x w) with h | h
  · rw [relu_of_nonneg h, relu_of_nonpos (neg_nonpos.mpr h), add_zero, abs_of_nonneg h]
  · rw [relu_of_nonpos h, relu_of_nonneg (neg_nonneg.mpr h), zero_add, abs_of_nonpos h]

/-- `Λ_{[w]} (⟨a, ·⟩ + relu ⟨x, ·⟩) = |⟨x, w⟩|` (a translate of the segment `[0, x]`). -/
theorem flagFun_singleton_dot_add_relu_dot (a x w : Fin m → ℝ) :
    flagFun [w] (fun y => dot a y + relu (dot x y)) = |dot x w| := by
  have e : (fun y => dot a y + relu (dot x y)) = (fun y => relu (dot x y)) + dot a := by
    funext y
    rw [Pi.add_apply, add_comm]
  rw [e, flagFun_add_dot (relu_dot_mem_SSpan x) a [w] le_rfl, flagFun_singleton_relu_dot]

end MaxNN.ParamidGeom
