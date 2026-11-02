import MaxCaterpillar.Fiber.BinaryPatterns

set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.BinaryPatterns

example {N h₁ h₂ : ℕ} (a : Network N h₁ h₂) (x : Point N) (j : Fin h₁) :
    a.firstBinary x j = true ↔ 0 < (∑ i,a.W₁ j i*x i)+a.b₁ j :=
  Network.firstBinary_eq_true_iff a x j
example {N h₁ h₂ : ℕ} (a : Network N h₁ h₂) (x : Point N) (k : Fin h₂) :
    a.secondBinary x k = true ↔ 0 < (∑ j,a.W₂ k j*a.firstHidden x j)+a.b₂ k :=
  Network.secondBinary_eq_true_iff a x k

example (t : ℝ) (ht : 0 ≤ t) : ∀ x,(net t).eval x = Maximum 4 x := net_eval t ht
example (t : ℝ) : (net t).HasZeroBiases := net_zeroBiases t
example (t : ℝ) (k : Fin 3) : (net t).w₃ k ≠ 0 := output_weights_nonzero t k
example (t : ℝ) (j : Fin 6) : ∃ i,(net t).W₁ j i ≠ 0 := first_rows_nonzero t j
example {h₁ h₂ : ℕ} (a : Network 4 h₁ h₂)
    (ha : ∀ x,a.eval x = Maximum 4 x) : 6 ≤ h₁ ∧ 3 ≤ h₂ := widths_minimal a ha

noncomputable example : Path zeroExact oneExact := exactPath
noncomputable example : Path (hybridExact 1 (by norm_num)) oneExact := strictPath
example (t : unitInterval) : (strictPath t).val.HasZeroBiases := strictPath_zeroBiases t
example (t : unitInterval) (k : Fin 3) : (strictPath t).val.w₃ k ≠ 0 := strictPath_output_nonzero t k
example : (hybridNet 1).firstBinary strictWitness 2 = false ∧
    (net 1).firstBinary strictWitness 2 = true ∧
    (hybridNet 1).secondBinary strictWitness 1 = false ∧
    (net 1).secondBinary strictWitness 1 = true := strict_binary_gate_changes

example : ConnectedComponents.mk zeroExact = ConnectedComponents.mk oneExact :=
  same_exact_component

example : (net 0).firstHidden diagonal = ![0,0,0,0,1,0] := firstHidden_zero_diagonal
example : (net 1).firstHidden diagonal = ![0,0,2,0,1,0] := firstHidden_one_diagonal
example : (net 0).secondHidden diagonal = ![1,0,0] := secondHidden_zero_diagonal
example : (net 1).secondHidden diagonal = ![4,3,0] := secondHidden_one_diagonal

example : (net 0).firstBinary diagonal ≠ (net 1).firstBinary diagonal ∧
    (net 0).secondBinary diagonal ≠ (net 1).secondBinary diagonal := binary_patterns_differ

example : ∃ a b : ExactFiber 4 6 3,
    Joined a b ∧ a.val.HasZeroBiases ∧ b.val.HasZeroBiases ∧
    (∀ k,a.val.w₃ k ≠ 0 ∧ b.val.w₃ k ≠ 0) ∧
    a.val.firstActiveCount diagonal = 1 ∧ b.val.firstActiveCount diagonal = 2 ∧
    a.val.secondActiveCount diagonal = 1 ∧ b.val.secondActiveCount diagonal = 2 :=
  connected_binary_pattern_counterexample

example : ∃ a b : ExactFiber 4 6 3,
    Joined a b ∧ a.val.HasZeroBiases ∧ b.val.HasZeroBiases ∧
    (∀ k,a.val.w₃ k ≠ 0 ∧ b.val.w₃ k ≠ 0) ∧
    a.val.firstPreactivation strictWitness 2 = -1 ∧
    b.val.firstPreactivation strictWitness 2 = 1 ∧
    a.val.secondPreactivation strictWitness 1 = -1 ∧
    b.val.secondPreactivation strictWitness 1 = 2 ∧
    a.val.firstActiveCount diagonal = 1 ∧ b.val.firstActiveCount diagonal = 2 ∧
    a.val.secondActiveCount diagonal = 1 ∧ b.val.secondActiveCount diagonal = 2 :=
  strict_connected_binary_pattern_counterexample

#check @Network.firstBinary_eq_true_iff
#check @Network.secondBinary_eq_true_iff
#check @net_eval
#check @connected_binary_pattern_counterexample
#check @strict_connected_binary_pattern_counterexample
#print axioms net_eval
#print axioms continuous_net
#print axioms first_rows_nonzero
#print axioms widths_minimal
#print axioms same_exact_component
#print axioms binary_patterns_differ
#print axioms connected_binary_pattern_counterexample
#print axioms hybridNet_eval
#print axioms strict_connected_binary_pattern_counterexample

#print axioms strictPath_zeroBiases
#print axioms strictPath_output_nonzero
#print axioms strict_binary_gate_changes
