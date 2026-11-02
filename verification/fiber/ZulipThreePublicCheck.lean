import MaxCaterpillar

set_option autoImplicit false
noncomputable section
open MaxCaterpillar MaxCaterpillar.Fiber

example : Nontrivial (ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  max4_6_5_at_least_two_components

example : Nonempty (Fin 65 ↪ ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  max4_6_5_at_least_65_components

example : Nonempty (ConnectedComponents (SymmetryQuotient 4 6 5) ≃ Fin 65) :=
  max4_6_5_has_65_components

example : ∃ a b : ExactFiber 4 6 3,
    Joined a b ∧ a.val.HasZeroBiases ∧ b.val.HasZeroBiases ∧
    (∀ z, a.val.firstHidden z = b.val.firstHidden z) ∧
    (∀ z, a.val.secondHidden z = b.val.secondHidden z) ∧
    a.val.interchangeFirst NaturalInterventions.base NaturalInterventions.donor 4 = 0 ∧
    b.val.interchangeFirst NaturalInterventions.base NaturalInterventions.donor 4 = 1 :=
  NaturalInterventions.connected_natural_activation_counterexample

open GatingAbstractions in
example :
    (∀ x, (family 1).eval x = Maximum 4 x) ∧
    (∀ x, (family 2).eval x = Maximum 4 x) ∧
    SameCompleteGates (family 1) (family 2) ∧
    ¬ Refines (family 1).secondHidden (family 2).secondHidden ∧
    ¬ Refines (family 2).secondHidden (family 1).secondHidden ∧
    Joined oneExact twoExact ∧
    HasSmoothRegularFiberChartAt (V := Fin 28 → ℝ) (W := Fin 17 → ℝ)
      {p : Fin 45 → ℝ | ∀ x : Point 4, (fromRaw p).eval x = Maximum 4 x}
      (toRaw (family 1)) ∧
    HasSmoothRegularFiberChartAt (V := Fin 28 → ℝ) (W := Fin 17 → ℝ)
      {p : Fin 45 → ℝ | ∀ x : Point 4, (fromRaw p).eval x = Maximum 4 x}
      (toRaw (family 2)) := regular_same_gate_exact_counterexample

open BinaryPatterns in
example : ∃ a b : ExactFiber 4 6 3,
    Joined a b ∧ a.val.HasZeroBiases ∧ b.val.HasZeroBiases ∧
    (∀ k, a.val.w₃ k ≠ 0 ∧ b.val.w₃ k ≠ 0) ∧
    a.val.firstPreactivation strictWitness 2 = -1 ∧
    b.val.firstPreactivation strictWitness 2 = 1 ∧
    a.val.secondPreactivation strictWitness 1 = -1 ∧
    b.val.secondPreactivation strictWitness 1 = 2 ∧
    a.val.firstActiveCount diagonal = 1 ∧ b.val.firstActiveCount diagonal = 2 ∧
    a.val.secondActiveCount diagonal = 1 ∧ b.val.secondActiveCount diagonal = 2 :=
  strict_connected_binary_pattern_counterexample

example {N h₁ h₂ : ℕ} [NeZero N] (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x, a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x, a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k, a.val.w₃ k ≠ 0) (hb : ∀ k, b.val.w₃ k ≠ 0)
    (hsign : ∀ k, 0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) : Joined a b :=
  BinaryPatterns.joined_of_global_binary_maps_output_signs a b hg₁ hg₂ ha hb hsign

#print axioms max4_6_5_at_least_two_components
#print axioms max4_6_5_at_least_65_components
#print axioms max4_6_5_has_65_components
#print axioms NaturalInterventions.connected_natural_activation_counterexample
#print axioms GatingAbstractions.regular_same_gate_exact_counterexample
#print axioms BinaryPatterns.strict_connected_binary_pattern_counterexample
#print axioms BinaryPatterns.joined_of_global_binary_maps_output_signs
