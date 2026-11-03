import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Model

/-! The linear bound has a nonempty boundary case: one convex shallow
preactivation, one positive outer fold, and a linear remainder compute MAX3. -/
set_option autoImplicit false

namespace MaxCaterpillar.Max5Optimal.ConvexCores.Nonvacuity
open BigOperators Frontier

private lemma maximum_three_explicit (x : Point 3) :
    Maximum 3 x = max (max (x 0) (x 1)) (x 2) := by
  refine le_antisymm ((Maximum_le_iff _ _).2 fun i => ?_)
    (max_le (max_le (le_Maximum x 0) (le_Maximum x 1)) (le_Maximum x 2))
  fin_cases i
  · exact le_max_of_le_left (le_max_left _ _)
  · exact le_max_of_le_left (le_max_right _ _)
  · exact le_max_right _ _

private lemma relu_sub_add_explicit (a b : ℝ) : relu (b - a) + a = max a b := by
  unfold relu
  rcases le_total a b with h | h
  · rw [max_eq_right (by linarith), max_eq_right h]; ring
  · rw [max_eq_left (by linarith), max_eq_left h]; ring

noncomputable def core (x : Point 3) : ℝ :=
  lin ![1, 0, -1] x + relu (lin ![-1, 1, 0] x)

theorem core_formula (x : Point 3) :
    core x = x 0 - x 2 + relu (x 1 - x 0) := by
  simp [core, lin, Fin.sum_univ_succ]
  congr 2 <;> ring

theorem core_raw (x : Point 3) :
    core x = lin ![1, 0, -1] x + 0 +
      ∑ _j : Fin 1, (1 : ℝ) * relu (lin ![-1, 1, 0] x + 0) := by
  simp [core]

theorem core_max (x : Point 3) :
    core x = max (x 0 - x 2) (x 1 - x 2) := by
  rw [core_formula, show x 1 - x 0 = (x 1 - x 2) - (x 0 - x 2) by ring,
    add_comm, relu_sub_add_explicit]

private theorem convex_difference (i j : Fin 3) :
    ConvexOn ℝ Set.univ (fun x : Point 3 => x i - x j) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b _ _ _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

theorem core_convex : ConvexOn ℝ Set.univ core := by
  have h := (convex_difference 0 2).sup (convex_difference 1 2)
  convert h using 1
  funext x
  exact core_max x

theorem core_shallow : IsShallow core := by
  simpa only [add_zero] using
    (IsShallow.affine (![1, 0, -1] : Point 3) 0).add
      (IsShallow.hinge (![-1, 1, 0] : Point 3) 0)

theorem remainder_shallow : IsShallow (fun x : Point 3 => x 2) :=
  (IsShallow.affine (![0, 0, 1] : Point 3) 0).congr
    (fun x => by simp [lin, Fin.sum_univ_succ])

theorem core_eval (x : Point 3) : x 2 + relu (core x) = Maximum 3 x := by
  rw [core_max, max_sub_sub_right, add_comm, relu_sub_add_explicit,
    maximum_three_explicit, max_comm]

noncomputable def maxThree : ConvexRepresentation 3 (Fin 1) where
  remainder := fun x => x 2
  core := fun _ => core
  weight := fun _ => 1
  shallow_remainder := remainder_shallow
  shallow_core := fun _ => core_shallow
  convex_core := fun _ => core_convex
  computes := fun x => by simpa using core_eval x

theorem boundary_nonempty : Nonempty (ConvexRepresentation 3 (Fin 1)) := ⟨maxThree⟩

#check @core_raw
#check @boundary_nonempty
#print axioms core_raw
#print axioms core_eval
#print axioms core_convex
#print axioms boundary_nonempty

end MaxCaterpillar.Max5Optimal.ConvexCores.Nonvacuity
