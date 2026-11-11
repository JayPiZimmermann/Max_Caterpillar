import MaxCaterpillar.Fiber.GatingAbstractions

set_option autoImplicit false
open MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.GatingAbstractions

example (c : ℝ) (hc : 0 ≤ c) : ∀ x, (family c).eval x = Maximum 4 x :=
  family_eval c hc

example (c : ℝ) : (family c).HasZeroBiases := family_zeroBiases c

example {N h₁ h₂ : ℕ} (a b : Network N h₁ h₂) :
    SameCompleteGates a b ↔
      (∀ x j, (firstPre a x j < 0 ↔ firstPre b x j < 0) ∧
        (firstPre a x j = 0 ↔ firstPre b x j = 0) ∧
        (0 < firstPre a x j ↔ 0 < firstPre b x j)) ∧
      (∀ x k, (secondPre a x k < 0 ↔ secondPre b x k < 0) ∧
        (secondPre a x k = 0 ↔ secondPre b x k = 0) ∧
        (0 < secondPre a x k ↔ 0 < secondPre b x k)) := Iff.rfl

example (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    SameCompleteGates (family c) (family d) :=
  family_same_complete_gates c d hc hd

example (c : ℝ) (hc : 0 ≤ c) :
    (family c).secondHidden inputX = (family c).secondHidden inputY ↔ c = 1 :=
  mergeXY_iff c hc

example (c : ℝ) (hc : 0 ≤ c) :
    (family c).secondHidden inputX = (family c).secondHidden inputZ ↔ c = 2 :=
  mergeXZ_iff c hc

example {X Y Z : Type*} (H : X → Y) (K : X → Z) :
    Refines H K ↔ ∀ x y, H x = H y → K x = K y := Iff.rfl

example :
    ¬ Refines (family 1).secondHidden (family 2).secondHidden ∧
      ¬ Refines (family 2).secondHidden (family 1).secondHidden :=
  family_partitions_incomparable

example :
    (¬ ∃ Q : (Fin 3 → ℝ) → (Fin 3 → ℝ),
      ∀ x, (family 2).secondHidden x = Q ((family 1).secondHidden x)) ∧
    (¬ ∃ Q : (Fin 3 → ℝ) → (Fin 3 → ℝ),
      ∀ x, (family 1).secondHidden x = Q ((family 2).secondHidden x)) :=
  no_representation_recoding

example : Continuous (fun t : ℝ => family (1+t)) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, (family (1+t)).eval x = Maximum 4 x :=
  continuous_exact_segment

noncomputable example : Path oneExact twoExact := exactPath
example : Joined oneExact twoExact := exact_points_joined

example (s t : unitInterval) :
    SameCompleteGates (exactPath s).val (exactPath t).val := exactPath_gates_fixed s t

example :
    (∀ x, (family 1).eval x = Maximum 4 x) ∧
    (∀ x, (family 2).eval x = Maximum 4 x) ∧
    SameCompleteGates (family 1) (family 2) ∧
    ¬ Refines (family 1).secondHidden (family 2).secondHidden ∧
    ¬ Refines (family 2).secondHidden (family 1).secondHidden :=
  same_gates_different_representations

#check @family_same_complete_gates
#check @same_gates_different_representations
#check @no_representation_recoding
#check @exactPath_gates_fixed
#print axioms family_eval
#print axioms family_same_complete_gates
#print axioms mergeXY_iff
#print axioms mergeXZ_iff
#print axioms family_partitions_incomparable
#print axioms no_representation_recoding
#print axioms continuous_exact_segment
#print axioms exactPath_gates_fixed
#print axioms exact_points_joined
#print axioms same_gates_different_representations
