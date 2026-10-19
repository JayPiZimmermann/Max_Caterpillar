import MaxNN.Constructions.Paramid.Geom.Germ
import MaxNN.Constructions.Paramid.Geom.Doubling

/-!
# Germs of paramid units

Module `M-UnitGerm` of the geometric core of `∀ n, MAX n ∈ ReLUClass n 2`
(`work/depth2_simplex/lean_core/BLUEPRINT.md`).

For an apex offset `γ`, a finite label set `V` and a direction `u` in `ℝ^m` write

* `A = ⟨γ, u⟩ + ∑_{v ∈ V} relu ⟨v, u⟩`, the inner sum of `paramidOn γ V` at `u`
  (so `paramidOn γ V u = relu A`);
* `P = {v ∈ V | 0 < ⟨v, u⟩}` and `Z = {v ∈ V | ⟨v, u⟩ = 0}`.

The germ at `u` of `paramidOn γ V y = relu (⟨γ, y⟩ + ∑_{v ∈ V} relu ⟨v, y⟩)`
(`unitGerm γ V u`, `isGerm_paramidOn`) is

* `0` if `A < 0`;
* `y ↦ ⟨γ + ∑_P v, y⟩ + ∑_{v ∈ Z} relu ⟨v, y⟩` if `0 < A`: the support function of the face
  `{γ + ∑_P v + ∑_J v | J ⊆ Z}` of the base parallelepiped.  It is a point plus segments, hence
  lies in `LSpan m 1` (`unitGerm_pos_mem_LSpan`);
* `paramidOn (γ + ∑_P v) Z` if `A = 0`: the cone over that face.

Hence `germDiff u (paramidOn γ V) = unitGerm γ V u − unitGerm γ V (−u)` (`germDiff_paramidOn`).
The proof is the `relu` germ calculus of `Geom/Germ.lean`.  A hinge `relu ⟨v, ·⟩` has germ
`⟨v, ·⟩`, `0` or `relu ⟨v, ·⟩` according to the sign of `⟨v, u⟩`.  The outer `relu` is treated
the same way according to the sign of `A`.

Further statements:

* `unitGerm_eq_hS_face`: `unitGerm γ V u = hS (face u (coneVertsOn γ V))`, by uniqueness of
  germs and `paramidOn_eq_hS`.  This is the bridge to the face descriptions of
  `Geom/Boundary/ConeFaces.lean`;
* `unitGerm_mem_SSpan`, and `unitGerm_mem_LSpan` (`∈ LSpan m (|Z| + 1)` in every case);
* the configurations met by the boundary formula:
  - `unitGerm_of_forall_orth`: the cone lies in `u^⊥`; then `germDiff_paramidOn_of_forall_orth`;
  - `unitGerm_of_forall_orth_of_pos`: the base, all labels in `u^⊥` and `0 < ⟨γ, u⟩`;
  - `unitGerm_of_single_pos`, `unitGerm_of_single_neg`: exactly one label `v₀` crosses `u^⊥`.
    The germ is then the lateral facet `[γ + v₀; V ∖ v₀]`, resp. `[γ; V ∖ v₀]`.

Helpers live in the namespace `MaxNN.ParamidGeom.UnitGermAux`.
-/

namespace MaxNN.ParamidGeom

open BigOperators

variable {m : ℕ}

/-! ## The germ of a paramid unit -/

/-- **Germ of a paramid unit** at `u`.  With `A = ⟨γ, u⟩ + ∑_{v ∈ V} relu ⟨v, u⟩`,
`P = {v ∈ V | 0 < ⟨v, u⟩}` and `Z = {v ∈ V | ⟨v, u⟩ = 0}`: `0` if `A < 0`;
`y ↦ ⟨γ + ∑_P v, y⟩ + ∑_{v ∈ Z} relu ⟨v, y⟩` if `0 < A`; `paramidOn (γ + ∑_P v) Z` if
`A = 0`. -/
noncomputable def unitGerm (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    (Fin m → ℝ) → ℝ :=
  if dot γ u + ∑ v in V, relu (dot v u) < 0 then 0
  else if 0 < dot γ u + ∑ v in V, relu (dot v u) then
    fun y => dot (γ + ∑ v in V.filter (fun v => 0 < dot v u), v) y +
      ∑ v in V.filter (fun v => dot v u = 0), relu (dot v y)
  else paramidOn (γ + ∑ v in V.filter (fun v => 0 < dot v u), v)
    (V.filter (fun v => dot v u = 0))

/-- `A < 0`: the germ vanishes. -/
theorem unitGerm_of_neg {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)} {u : Fin m → ℝ}
    (hA : dot γ u + ∑ v in V, relu (dot v u) < 0) : unitGerm γ V u = 0 := by
  unfold unitGerm
  rw [if_pos hA]

/-- `0 < A`: the germ is the support function of the parallelepiped face. -/
theorem unitGerm_of_pos {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)} {u : Fin m → ℝ}
    (hA : 0 < dot γ u + ∑ v in V, relu (dot v u)) :
    unitGerm γ V u = fun y => dot (γ + ∑ v in V.filter (fun v => 0 < dot v u), v) y +
      ∑ v in V.filter (fun v => dot v u = 0), relu (dot v y) := by
  unfold unitGerm
  rw [if_neg (not_lt.mpr hA.le), if_pos hA]

/-- `A = 0`: the germ is the cone over the parallelepiped face. -/
theorem unitGerm_of_eq_zero {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)} {u : Fin m → ℝ}
    (hA : dot γ u + ∑ v in V, relu (dot v u) = 0) :
    unitGerm γ V u = paramidOn (γ + ∑ v in V.filter (fun v => 0 < dot v u), v)
      (V.filter (fun v => dot v u = 0)) := by
  unfold unitGerm
  rw [if_neg (not_lt.mpr hA.ge), if_neg (not_lt.mpr hA.le)]

namespace UnitGermAux

/-! ## Helpers -/

/-- `IsGerm` sees its germ only through the values. -/
theorem isGerm_congr_right {f g g' : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} (h : IsGerm f u g)
    (e : ∀ y, g y = g' y) : IsGerm f u g' := by
  have e' : g = g' := funext e
  rw [← e']
  exact h

/-- `⟨v, −u⟩ = −⟨v, u⟩`. -/
theorem dot_neg_right (v u : Fin m → ℝ) : dot v (-u) = -dot v u := by
  unfold dot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.neg_apply, mul_neg]

/-- The labels positive on `−u` are the labels negative on `u`. -/
theorem filter_dot_neg_pos (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    V.filter (fun v => 0 < dot v (-u)) = V.filter (fun v => dot v u < 0) := by
  refine Finset.filter_congr fun v _ => ?_
  rw [dot_neg_right, neg_pos]

/-- The labels orthogonal to `−u` are the labels orthogonal to `u`. -/
theorem filter_dot_neg_eq_zero (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    V.filter (fun v => dot v (-u) = 0) = V.filter (fun v => dot v u = 0) := by
  refine Finset.filter_congr fun v _ => ?_
  rw [dot_neg_right, neg_eq_zero]

/-- `∑_{v ∈ V} relu ⟨v, u⟩ = ∑_{v ∈ P} ⟨v, u⟩`. -/
theorem sum_relu_dot_eq_sum_filter (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    ∑ v in V, relu (dot v u) = ∑ v in V.filter (fun v => 0 < dot v u), dot v u := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : 0 < dot v u
  · rw [if_pos h, relu_of_nonneg h.le]
  · rw [if_neg h, relu_of_nonpos (not_lt.mp h)]

/-- A paramid unit without labels is a hinge: `paramidOn v ∅ = relu ⟨v, ·⟩`. -/
theorem paramidOn_empty (v y : Fin m → ℝ) : paramidOn v ∅ y = relu (dot v y) := by
  unfold paramidOn
  rw [Finset.sum_empty, add_zero]

/-- A linear form is the support function of a point. -/
theorem dot_mem_LSpan (p : Fin m → ℝ) (k : ℕ) : dot p ∈ LSpan m k := by
  unfold LSpan
  exact Submodule.subset_span (dot_mem_lowerDimSupport p k)

/-- A hinge `relu ⟨v, ·⟩` is the support function of the segment `{0, v}`, so it lies in
`LSpan m 1`. -/
theorem relu_dot_mem_LSpan_one (v : Fin m → ℝ) : (fun y => relu (dot v y)) ∈ LSpan m 1 := by
  have h := paramidOn_mem_LSpan v (∅ : Finset (Fin m → ℝ))
  rw [Finset.card_empty, zero_add] at h
  have e : paramidOn v ∅ = fun y => relu (dot v y) := funext (paramidOn_empty v)
  rw [e] at h
  exact h

/-- **Germ of a hinge** `relu ⟨v, ·⟩` at `u`: `⟨v, ·⟩` if `0 < ⟨v, u⟩`, `relu ⟨v, ·⟩` if
`⟨v, u⟩ = 0`, `0` if `⟨v, u⟩ < 0`, written as a sum of two `if`s. -/
theorem isGerm_relu_dot (v u : Fin m → ℝ) :
    IsGerm (fun y => relu (dot v y)) u
      (fun y => (if 0 < dot v u then dot v y else 0) +
        (if dot v u = 0 then relu (dot v y) else 0)) := by
  rcases lt_trichotomy (dot v u) 0 with h | h | h
  · refine isGerm_congr_right ((isGerm_dot v u).relu_of_neg h) fun y => ?_
    rw [if_neg (not_lt.mpr h.le), if_neg h.ne, add_zero, Pi.zero_apply]
  · refine isGerm_congr_right ((isGerm_dot v u).relu_of_eq_zero h) fun y => ?_
    rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add]
  · refine isGerm_congr_right ((isGerm_dot v u).relu_of_pos h) fun y => ?_
    rw [if_pos h, if_neg h.ne', add_zero]

/-- **Germ of the inner sum** `y ↦ ⟨γ, y⟩ + ∑_{v ∈ V} relu ⟨v, y⟩` at `u`:
`y ↦ ⟨γ + ∑_P v, y⟩ + ∑_{v ∈ Z} relu ⟨v, y⟩`. -/
theorem isGerm_inner (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    IsGerm (fun y => dot γ y + ∑ v in V, relu (dot v y)) u
      (fun y => dot (γ + ∑ v in V.filter (fun v => 0 < dot v u), v) y +
        ∑ v in V.filter (fun v => dot v u = 0), relu (dot v y)) := by
  have h : IsGerm (fun y => dot γ y + ∑ v in V, relu (dot v y)) u
      (fun y => dot γ y + ∑ v in V, ((if 0 < dot v u then dot v y else 0) +
        (if dot v u = 0 then relu (dot v y) else 0))) :=
    (isGerm_dot γ u).add (IsGerm.sum V fun v _ => isGerm_relu_dot v u)
  refine isGerm_congr_right h fun y => ?_
  rw [Finset.sum_add_distrib, SupportCut.dot_add_left, DoublingAux.dot_sum_left,
    Finset.sum_filter, Finset.sum_filter, add_assoc]

end UnitGermAux

open UnitGermAux

/-! ## The germ of `paramidOn` -/

/-- **The germ of a paramid unit** at `u` is `unitGerm γ V u`. -/
theorem isGerm_paramidOn (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    IsGerm (paramidOn γ V) u (unitGerm γ V u) := by
  have hin := isGerm_inner γ V u
  rcases lt_trichotomy (dot γ u + ∑ v in V, relu (dot v u)) 0 with h | h | h
  · rw [unitGerm_of_neg h]
    exact hin.relu_of_neg h
  · rw [unitGerm_of_eq_zero h]
    exact hin.relu_of_eq_zero h
  · rw [unitGerm_of_pos h]
    exact hin.relu_of_pos h

theorem germ_paramidOn (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    germ (paramidOn γ V) u = unitGerm γ V u :=
  germ_eq_of_isGerm (isGerm_paramidOn γ V u)

/-- **Facet datum of a paramid unit**: `germDiff u (paramidOn γ V) = unitGerm γ V u −
unitGerm γ V (−u)`. -/
theorem germDiff_paramidOn (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    germDiff u (paramidOn γ V) = unitGerm γ V u - unitGerm γ V (-u) := by
  rw [germDiff_eq_sub, germ_paramidOn, germ_paramidOn]

/-- The germ is the support function of the face of the cone `coneVertsOn γ V` in direction
`u`. -/
theorem unitGerm_eq_hS_face (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    unitGerm γ V u = hS (face u (coneVertsOn γ V)) := by
  have h₂ := isGerm_hS (DoublingAux.coneVertsOn_nonempty γ V) u
  rw [← paramidOn_eq_hS γ V] at h₂
  exact (isGerm_paramidOn γ V u).unique h₂

theorem unitGerm_mem_SSpan (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    unitGerm γ V u ∈ SSpan m := by
  rw [← germ_paramidOn]
  exact germ_mem_SSpan (paramidOn_mem_SSpan γ V) u

/-! ## Dimension of the germ -/

/-- **`0 < A`: the germ is a point plus segments** (`⟨γ + ∑_P v, ·⟩` plus the hinges of the
labels orthogonal to `u`), hence lies in `LSpan m 1`. -/
theorem unitGerm_pos_mem_LSpan {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)} {u : Fin m → ℝ}
    (hA : 0 < dot γ u + ∑ v in V, relu (dot v u)) : unitGerm γ V u ∈ LSpan m 1 := by
  rw [unitGerm_of_pos hA]
  have e : (fun y => dot (γ + ∑ v in V.filter (fun v => 0 < dot v u), v) y +
        ∑ v in V.filter (fun v => dot v u = 0), relu (dot v y)) =
      dot (γ + ∑ v in V.filter (fun v => 0 < dot v u), v) +
        ∑ v in V.filter (fun v => dot v u = 0), (fun y => relu (dot v y)) := by
    funext y
    rw [Pi.add_apply, Finset.sum_apply]
  rw [e]
  exact Submodule.add_mem _ (dot_mem_LSpan _ 1)
    (Submodule.sum_mem _ fun v _ => relu_dot_mem_LSpan_one v)

/-- In every case the germ lies in `LSpan m (|Z| + 1)`. -/
theorem unitGerm_mem_LSpan (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (u : Fin m → ℝ) :
    unitGerm γ V u ∈ LSpan m ((V.filter (fun v => dot v u = 0)).card + 1) := by
  rcases lt_trichotomy (dot γ u + ∑ v in V, relu (dot v u)) 0 with h | h | h
  · rw [unitGerm_of_neg h]
    exact Submodule.zero_mem _
  · rw [unitGerm_of_eq_zero h]
    exact paramidOn_mem_LSpan _ _
  · exact DoublingAux.LSpan_mono (Nat.le_add_left 1 _) (unitGerm_pos_mem_LSpan h)

/-! ## Special configurations -/

/-- **Cone inside `u^⊥`.**  If `γ` and every label are orthogonal to `u`, the germ is the unit
itself. -/
theorem unitGerm_of_forall_orth {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)} {u : Fin m → ℝ}
    (hV : ∀ v ∈ V, dot v u = 0) (hγ : dot γ u = 0) : unitGerm γ V u = paramidOn γ V := by
  have hP : V.filter (fun v => 0 < dot v u) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v hv hpos
    rw [hV v hv] at hpos
    exact lt_irrefl 0 hpos
  have hZ : V.filter (fun v => dot v u = 0) = V := Finset.filter_true_of_mem hV
  have hA : dot γ u + ∑ v in V, relu (dot v u) = 0 := by
    rw [sum_relu_dot_eq_sum_filter, hP, Finset.sum_empty, hγ, add_zero]
  rw [unitGerm_of_eq_zero hA, hP, hZ, Finset.sum_empty, add_zero]

/-- If `γ` and every label are orthogonal to `u`, the unit has no facet datum in direction
`u`. -/
theorem germDiff_paramidOn_of_forall_orth {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)}
    {u : Fin m → ℝ} (hV : ∀ v ∈ V, dot v u = 0) (hγ : dot γ u = 0) :
    germDiff u (paramidOn γ V) = 0 := by
  have hV' : ∀ v ∈ V, dot v (-u) = 0 := fun v hv => by rw [dot_neg_right, hV v hv, neg_zero]
  have hγ' : dot γ (-u) = 0 := by rw [dot_neg_right, hγ, neg_zero]
  rw [germDiff_paramidOn, unitGerm_of_forall_orth hV hγ, unitGerm_of_forall_orth hV' hγ',
    sub_self]

/-- **Base.**  If every label is orthogonal to `u` and `0 < ⟨γ, u⟩`, the germ is the support
function `⟨γ, ·⟩ + ∑_{v ∈ V} relu ⟨v, ·⟩` of the base parallelepiped. -/
theorem unitGerm_of_forall_orth_of_pos {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)}
    {u : Fin m → ℝ} (hV : ∀ v ∈ V, dot v u = 0) (hγ : 0 < dot γ u) :
    unitGerm γ V u = fun y => dot γ y + ∑ v in V, relu (dot v y) := by
  have hP : V.filter (fun v => 0 < dot v u) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v hv hpos
    rw [hV v hv] at hpos
    exact lt_irrefl 0 hpos
  have hZ : V.filter (fun v => dot v u = 0) = V := Finset.filter_true_of_mem hV
  have hA : 0 < dot γ u + ∑ v in V, relu (dot v u) := by
    rw [sum_relu_dot_eq_sum_filter, hP, Finset.sum_empty, add_zero]
    exact hγ
  rw [unitGerm_of_pos hA, hP, hZ, Finset.sum_empty, add_zero]

/-- **Lateral facet through `γ + v₀`.**  If `v₀ ∈ V` is the only label not orthogonal to `u`,
`0 < ⟨v₀, u⟩` and `⟨γ + v₀, u⟩ = 0`, the germ is the unit `[γ + v₀; V ∖ v₀]`. -/
theorem unitGerm_of_single_pos {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)} {u v₀ : Fin m → ℝ}
    (hv₀ : v₀ ∈ V) (hb : 0 < dot v₀ u) (hrest : ∀ v ∈ V, v ≠ v₀ → dot v u = 0)
    (hA : dot γ u + dot v₀ u = 0) :
    unitGerm γ V u = paramidOn (γ + v₀) (V.erase v₀) := by
  have hP : V.filter (fun v => 0 < dot v u) = {v₀} := by
    ext v
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hpos⟩
      by_contra hne
      rw [hrest v hv hne] at hpos
      exact lt_irrefl 0 hpos
    · rintro rfl
      exact ⟨hv₀, hb⟩
  have hZ : V.filter (fun v => dot v u = 0) = V.erase v₀ := by
    ext v
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hv, hz⟩
      refine ⟨?_, hv⟩
      rintro rfl
      rw [hz] at hb
      exact lt_irrefl 0 hb
    · rintro ⟨hne, hv⟩
      exact ⟨hv, hrest v hv hne⟩
  have hA' : dot γ u + ∑ v in V, relu (dot v u) = 0 := by
    rw [sum_relu_dot_eq_sum_filter, hP, Finset.sum_singleton]
    exact hA
  rw [unitGerm_of_eq_zero hA', hP, hZ, Finset.sum_singleton]

/-- **Lateral facet through `γ`.**  If `v₀` is the only label not orthogonal to `u`,
`⟨v₀, u⟩ < 0` and `⟨γ, u⟩ = 0`, the germ is the unit `[γ; V ∖ v₀]`. -/
theorem unitGerm_of_single_neg {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)} {u v₀ : Fin m → ℝ}
    (hb : dot v₀ u < 0) (hrest : ∀ v ∈ V, v ≠ v₀ → dot v u = 0) (hγ : dot γ u = 0) :
    unitGerm γ V u = paramidOn γ (V.erase v₀) := by
  have hP : V.filter (fun v => 0 < dot v u) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v hv hpos
    by_cases hne : v = v₀
    · rw [hne] at hpos
      exact lt_irrefl 0 (lt_trans hpos hb)
    · rw [hrest v hv hne] at hpos
      exact lt_irrefl 0 hpos
  have hZ : V.filter (fun v => dot v u = 0) = V.erase v₀ := by
    ext v
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hv, hz⟩
      refine ⟨?_, hv⟩
      rintro rfl
      rw [hz] at hb
      exact lt_irrefl 0 hb
    · rintro ⟨hne, hv⟩
      exact ⟨hv, hrest v hv hne⟩
  have hA : dot γ u + ∑ v in V, relu (dot v u) = 0 := by
    rw [sum_relu_dot_eq_sum_filter, hP, Finset.sum_empty, hγ, add_zero]
  rw [unitGerm_of_eq_zero hA, hP, hZ, Finset.sum_empty, add_zero]

end MaxNN.ParamidGeom
