import MaxNN.Constructions.Paramid.Caterpillar.Endpoint
import MaxNN.Constructions.Paramid.Geom.UnitGerm

/-! # Block-direction germs of caterpillar units

The units in this file are actual max-of-pair-max functions. Their directional
germs use the existing analytic `ParamidGeom.germ` semantics. The cut word on
one side of the spine can be summed out by `endpoint_cancellation`.

This is a local endpoint-fibre theorem. The global reindexing into these fibres,
the coordinate and braid facets, and the resulting all-arity MAX identity are
not proved in this module. No network-width bound follows from this file alone.
-/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m r s : ℕ}

private theorem max_eq_add_relu (a b : ℝ) : max a b = a + relu (b - a) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, relu_of_nonneg (sub_nonneg.2 h)]
    ring
  · rw [max_eq_left h, relu_of_nonpos (sub_nonpos.2 h)]
    ring

theorem isGerm_max_of_eq {f g df dg : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ}
    (hf : IsGerm f u df) (hg : IsGerm g u dg) (heq : f u = g u) :
    IsGerm (fun y => max (f y) (g y)) u (fun y => max (df y) (dg y)) := by
  have h0 : (g - f) u = 0 := by change g u - f u = 0; rw [heq, sub_self]
  have h := hf.add ((hg.sub hf).relu_of_eq_zero h0)
  have he : (fun y => max (f y) (g y)) = f + (fun y => relu ((g - f) y)) := by
    funext y
    exact max_eq_add_relu _ _
  have hde : (fun y => max (df y) (dg y)) = df + (fun y => relu ((dg - df) y)) := by
    funext y
    exact max_eq_add_relu _ _
  rw [he, hde]
  exact h

theorem isGerm_max_of_lt {f g df dg : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ}
    (hf : IsGerm f u df) (hg : IsGerm g u dg) (hlt : f u < g u) :
    IsGerm (fun y => max (f y) (g y)) u dg := by
  have h0 : (f - g) u < 0 := sub_neg.2 hlt
  have h := hg.add ((hf.sub hg).relu_of_neg h0)
  have he : (fun y => max (f y) (g y)) = g + (fun y => relu ((f - g) y)) := by
    funext y
    rw [max_comm, max_eq_add_relu]
    rfl
  rw [he]
  simpa only [add_zero] using h

/-- Vertex values given by fixed points and the variable covector. -/
noncomputable def values (A : Fin (r + 1) → Fin m → ℝ) (y : Fin m → ℝ) : Fin (r + 1) → ℝ :=
  fun i => dot (A i) y

theorem isGerm_treeMax_of_constant (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (u : Fin m → ℝ) (c : ℝ)
    (hA : ∀ i, dot (A i) u = c) :
    IsGerm (fun y => treeMax (values A y) S) u (fun y => treeMax (values A y) S) := by
  apply IsGerm.sum
  intro j _
  exact isGerm_max_of_eq (isGerm_dot _ _) (isGerm_dot _ _)
    ((hA _).trans (hA _).symm)

theorem isGerm_pointedMax_of_constant (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (u : Fin m → ℝ) (c : ℝ)
    (hA : ∀ i, dot (A i) u = c) :
    IsGerm (fun y => pointedMax (values A y) S) u
      (fun y => pointedMax (values A y) S) := by
  exact ((isGerm_treeMax_of_constant A S u c hA).sub
    (IsGerm.sum Finset.univ fun i _ => isGerm_dot (A i) u)).add (isGerm_dot (A 0) u)

theorem isGerm_baseMax_of_constant (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (u : Fin m → ℝ) (c : ℝ)
    (hA : ∀ i, dot (A i) u = c) :
    IsGerm (fun y => baseMax (values A y) S) u (fun y => baseMax (values A y) S) := by
  exact (isGerm_pointedMax_of_constant A S u c hA).add (isGerm_dot (A (lastHead S)) u)

theorem max_dot_mem_LSpan_one (a b : Fin m → ℝ) :
    (fun y => max (dot a y) (dot b y)) ∈ LSpan m 1 := by
  have he : (fun y => max (dot a y) (dot b y)) =
      dot a + (fun y => relu (dot (b - a) y)) := by
    funext y
    rw [max_eq_add_relu]
    simp only [Pi.add_apply, dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [he]
  exact Submodule.add_mem _ (UnitGermAux.dot_mem_LSpan _ _)
    (UnitGermAux.relu_dot_mem_LSpan_one _)

theorem treeMax_mem_LSpan_one (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) :
    (fun y => treeMax (values A y) S) ∈ LSpan m 1 := by
  have h : (∑ j : Fin r, fun y => max (dot (A (parent S j.succ)) y)
      (dot (A j.succ) y)) ∈ LSpan m 1 :=
    Submodule.sum_mem _ fun _ _ => max_dot_mem_LSpan_one _ _
  have he : (fun y => treeMax (values A y) S) =
      ∑ j : Fin r, fun y => max (dot (A (parent S j.succ)) y) (dot (A j.succ) y) := by
    funext y
    simp only [treeMax, values, Finset.sum_apply]
  rwa [he]

theorem pointedMax_mem_LSpan_one (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) :
    (fun y => pointedMax (values A y) S) ∈ LSpan m 1 := by
  have hs : (fun y => ∑ j, dot (A j) y) ∈ LSpan m 1 := by
    have h : (∑ j, dot (A j)) ∈ LSpan m 1 :=
      Submodule.sum_mem _ fun _ _ => UnitGermAux.dot_mem_LSpan _ _
    have he : (fun y => ∑ j, dot (A j) y) = ∑ j, dot (A j) := by
      funext y
      rw [Finset.sum_apply]
    rwa [he]
  exact Submodule.add_mem _ (Submodule.sub_mem _ (treeMax_mem_LSpan_one A S) hs)
    (UnitGermAux.dot_mem_LSpan _ _)

theorem baseMax_mem_LSpan_one (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) :
    (fun y => baseMax (values A y) S) ∈ LSpan m 1 :=
  Submodule.add_mem _ (pointedMax_mem_LSpan_one A S)
    (UnitGermAux.dot_mem_LSpan _ _)

/-- The max expression obtained by joining two spine words at their adjacent
endpoints and adjoining the displayed apex. -/
noncomputable def joinedUnit (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1))) (y : Fin m → ℝ) : ℝ :=
  max (dot apex y) (pointedMax (values A y) S + baseMax (values B y) T +
    max (dot (A (lastHead S)) y) (dot (B 0) y) - dot (B 0) y)

/-- The crossing-edge endpoint disappears from the block-direction germ,
leaving the pointed first base. Normal values are specified explicitly. -/
theorem germ_joinedUnit_block (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1)))
    (u : Fin m → ℝ) (ha : dot apex u = 0)
    (hA : ∀ i, dot (A i) u = -1) (hB : ∀ i, dot (B i) u = 0) :
    germ (joinedUnit apex A B S T) u =
      fun y => max (dot apex y) (pointedMax (values A y) S + baseMax (values B y) T) := by
  have hcross := isGerm_max_of_lt (isGerm_dot (A (lastHead S)) u)
    (isGerm_dot (B 0) u) (by rw [hA, hB]; norm_num)
  have hinner := (((isGerm_pointedMax_of_constant A S u (-1) hA).add
    (isGerm_baseMax_of_constant B T u 0 hB)).add hcross).sub (isGerm_dot (B 0) u)
  have hvA : pointedMax (values A u) S = 0 := pointedMax_of_constant _ _ (-1) hA
  have hvB : baseMax (values B u) T = 0 := baseMax_of_constant _ _ 0 hB
  have hout := isGerm_max_of_eq (isGerm_dot apex u) hinner (by
    change dot apex u = pointedMax (values A u) S + baseMax (values B u) T +
      max (dot (A (lastHead S)) u) (dot (B 0) u) - dot (B 0) u
    rw [ha, hvA, hvB, hA, hB]
    norm_num)
  apply germ_eq_of_isGerm
  simpa only [Pi.add_apply, Pi.sub_apply, add_sub_cancel] using hout

/-- All endpoint choices cancel as actual analytic block-direction germs. -/
theorem sum_germ_joinedUnit_block_eq_zero (hr : 1 ≤ r) (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (T : Finset (Fin (s + 1))) (u : Fin m → ℝ) (ha : dot apex u = 0)
    (hA : ∀ i, dot (A i) u = -1) (hB : ∀ i, dot (B i) u = 0) (y : Fin m → ℝ) :
    ∑ S in (cutPositions r).powerset,
      (-1 : ℝ) ^ S.card * germ (joinedUnit apex A B S T) u y = 0 := by
  simp_rw [germ_joinedUnit_block apex A B _ T u ha hA hB]
  exact endpoint_join_cancellation r hr (values A y) (dot apex y) (baseMax (values B y) T)

/-- In the opposite block direction the outer maximum selects the base.
Its germ is a sum of pair maxima and linear functions. -/
theorem germ_joinedUnit_opposite_block (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1)))
    (u : Fin m → ℝ) (ha : dot apex u = 0)
    (hA : ∀ i, dot (A i) u = 1) (hB : ∀ i, dot (B i) u = 0) :
    germ (joinedUnit apex A B S T) u = fun y =>
      pointedMax (values A y) S + baseMax (values B y) T +
        dot (A (lastHead S)) y - dot (B 0) y := by
  have hcross' := isGerm_max_of_lt (isGerm_dot (B 0) u)
    (isGerm_dot (A (lastHead S)) u) (by rw [hA, hB]; norm_num)
  have hcross : IsGerm (fun y => max (dot (A (lastHead S)) y) (dot (B 0) y)) u
      (dot (A (lastHead S))) := by
    simpa only [max_comm] using hcross'
  have hinner := (((isGerm_pointedMax_of_constant A S u 1 hA).add
    (isGerm_baseMax_of_constant B T u 0 hB)).add hcross).sub (isGerm_dot (B 0) u)
  have hvA : pointedMax (values A u) S = 0 := pointedMax_of_constant _ _ 1 hA
  have hvB : baseMax (values B u) T = 0 := baseMax_of_constant _ _ 0 hB
  have hout := isGerm_max_of_lt (isGerm_dot apex u) hinner (by
    change dot apex u < pointedMax (values A u) S + baseMax (values B u) T +
      max (dot (A (lastHead S)) u) (dot (B 0) u) - dot (B 0) u
    rw [ha, hvA, hvB, hA, hB]
    norm_num)
  exact germ_eq_of_isGerm hout

theorem germ_joinedUnit_neg_block_mem_LSpan_one (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1)))
    (u : Fin m → ℝ) (ha : dot apex u = 0)
    (hA : ∀ i, dot (A i) u = -1) (hB : ∀ i, dot (B i) u = 0) :
    germ (joinedUnit apex A B S T) (-u) ∈ LSpan m 1 := by
  rw [germ_joinedUnit_opposite_block apex A B S T (-u)
    (by rw [UnitGermAux.dot_neg_right, ha, neg_zero])
    (fun i => by rw [UnitGermAux.dot_neg_right, hA i]; norm_num)
    (fun i => by rw [UnitGermAux.dot_neg_right, hB i, neg_zero])]
  exact Submodule.sub_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (pointedMax_mem_LSpan_one A S) (baseMax_mem_LSpan_one B T))
    (UnitGermAux.dot_mem_LSpan _ _)) (UnitGermAux.dot_mem_LSpan _ _)

/-- The full two-sided facet data of an endpoint fibre vanish modulo sums of
segment support functions. Both directional germs are the analytic germs. -/
theorem sum_germDiff_joinedUnit_block_mem_LSpan_one (hr : 1 ≤ r) (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (T : Finset (Fin (s + 1))) (u : Fin m → ℝ) (ha : dot apex u = 0)
    (hA : ∀ i, dot (A i) u = -1) (hB : ∀ i, dot (B i) u = 0) :
    (fun y => ∑ S in (cutPositions r).powerset,
      (-1 : ℝ) ^ S.card * germDiff u (joinedUnit apex A B S T) y) ∈ LSpan m 1 := by
  have he : (fun y => ∑ S in (cutPositions r).powerset,
        (-1 : ℝ) ^ S.card * germDiff u (joinedUnit apex A B S T) y) =
      -(∑ S in (cutPositions r).powerset,
        (-1 : ℝ) ^ S.card • germ (joinedUnit apex A B S T) (-u)) := by
    funext y
    simp only [germDiff, mul_sub, Finset.sum_sub_distrib, Pi.neg_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_germ_joinedUnit_block_eq_zero hr apex A B T u ha hA hB y, zero_sub]
  rw [he]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _
    (germ_joinedUnit_neg_block_mem_LSpan_one apex A B S T u ha hA hB))

end MaxNN.Caterpillar
