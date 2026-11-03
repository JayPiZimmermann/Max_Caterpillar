import research.sN.overnight_20261103.constants.FallingJoint

/-! Expanded checks for the exact actual-model budget and sharp scalar controls. -/
set_option autoImplicit false
namespace MaxCaterpillar.Overnight.Constants.FallingHalf.Check
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
variable {N n h₁ h₂ : ℕ}

theorem exact_model_type [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x=Maximum N x) (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N), S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      16*(∑ j : Fin h₁, (rowSupport (model.A j)).card.descFactorial 4)≤105*h₁ ∧
      8*(Finset.univ.filter (fun j : Fin h₁ => 3≤(rowSupport (model.A j)).card)).card≤h₁ :=
  exists_joint_model net hn hnet hpair

theorem equality_at_seven : 16*(7:ℕ).descFactorial 4=105*2^7 := by
  norm_num [Nat.descFactorial]

theorem equality_at_eight : 16*(8:ℕ).descFactorial 4=105*2^8 := by
  norm_num [Nat.descFactorial]

theorem joint_equality_at_three : 8*jointCost 3=105*2^3 := by
  norm_num [jointCost, Nat.descFactorial]

/-- Empty ambient and row families are included by the combinatorial theorem. -/
theorem empty_control :
    ∃ U : Finset (Fin 0), U.card=0 ∧
      8*(∑ j : Fin 0, if (∅ : Finset (Fin 0))⊆U
        then jointCost (∅ : Finset (Fin 0)).card else 0)≤105*0 := by
  exact ⟨∅, by simp⟩

#check @exact_model_type
#print axioms exact_model_type
#print axioms equality_at_seven
#print axioms equality_at_eight
#print axioms joint_equality_at_three
#print axioms empty_control
end MaxCaterpillar.Overnight.Constants.FallingHalf.Check
