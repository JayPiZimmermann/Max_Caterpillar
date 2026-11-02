import MaxCaterpillar.Fiber.NaturalInterventions

set_option autoImplicit false

open BigOperators MaxCaterpillar
open MaxCaterpillar.Fiber.NaturalInterventions
open MaxCaterpillar.Fiber unitInterval

-- These are the actual physical activation and intervention formulas.
example {N h₁ h₂ : ℕ} (a : Network N h₁ h₂) (x : Point N) :
    a.firstHidden x = fun j => relu ((∑ i, a.W₁ j i * x i) + a.b₁ j) := rfl

example {N h₁ h₂ : ℕ} (a : Network N h₁ h₂) (x : Point N) :
    a.secondHidden x = fun k => relu ((∑ j, a.W₂ k j * a.firstHidden x j) + a.b₂ k) := rfl

example {N h₁ h₂ : ℕ} (a : Network N h₁ h₂) (x y : Point N) (j : Fin h₁) :
    a.interchangeFirst x y j =
      a.fromFirstHidden (Function.update (a.firstHidden x) j (a.firstHidden y j)) := rfl

example (t : ℝ) : (net t).HasZeroBiases := net_zeroBiases t

example (t : ℝ) (ht : 0 ≤ t) (x : Point 4) : (net t).eval x = Maximum 4 x :=
  net_eval t ht x

example (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∀ x, (net s).firstHidden x = (net t).firstHidden x) ∧
      (∀ x, (net s).secondHidden x = (net t).secondHidden x) :=
  same_natural_hidden s t hs ht

example : (net 0).interchangeFirst base donor 4 = 0 := interchange_zero
example : (net 1).interchangeFirst base donor 4 = 1 := interchange_one

example :
    ∃ (a b : Network 4 6 3) (x y : Point 4) (j : Fin 6),
      a.HasZeroBiases ∧ b.HasZeroBiases ∧
      (∀ z, a.eval z = Maximum 4 z) ∧ (∀ z, b.eval z = Maximum 4 z) ∧
      (∀ z, a.firstHidden z = b.firstHidden z) ∧
      (∀ z, a.secondHidden z = b.secondHidden z) ∧
      a.interchangeFirst x y j = 0 ∧ b.interchangeFirst x y j = 1 :=
  natural_activation_counterexample

example {h₁ h₂ : ℕ} (a : Network 4 h₁ h₂)
    (ha : ∀ x, a.eval x = Maximum 4 x) : 6 ≤ h₁ ∧ 3 ≤ h₂ := widths_minimal a ha

example : Continuous net := continuous_net

noncomputable example : Path zeroExact oneExact := exactPath

example (s t : I) :
    (∀ x, (exactPath s).val.firstHidden x = (exactPath t).val.firstHidden x) ∧
      (∀ x, (exactPath s).val.secondHidden x = (exactPath t).val.secondHidden x) :=
  exactPath_hidden_fixed s t

example : ConnectedComponents.mk zeroExact = ConnectedComponents.mk oneExact :=
  same_exact_component

example :
    ∃ a b : ExactFiber 4 6 3,
      Joined a b ∧ a.val.HasZeroBiases ∧ b.val.HasZeroBiases ∧
      (∀ z, a.val.firstHidden z = b.val.firstHidden z) ∧
      (∀ z, a.val.secondHidden z = b.val.secondHidden z) ∧
      a.val.interchangeFirst base donor 4 = 0 ∧
      b.val.interchangeFirst base donor 4 = 1 :=
  connected_natural_activation_counterexample

#check @Network.firstHidden
#check @Network.secondHidden
#check @Network.fromFirstHidden
#check @Network.interchangeFirst
#check @net_eval
#check @same_natural_hidden
#check @natural_activation_counterexample
#check @widths_minimal
#print axioms net_zeroBiases
#print axioms firstHidden_net
#print axioms secondHidden_net
#print axioms same_natural_hidden
#print axioms net_eval
#print axioms interchange_zero
#print axioms interchange_one
#print axioms natural_activation_counterexample
#print axioms widths_minimal

#check @continuous_net
#check @exactPath
#check @same_exact_component
#check @connected_natural_activation_counterexample
#print axioms continuous_net
#print axioms exactPath
#print axioms exactPath_hidden_fixed
#print axioms same_exact_component
#print axioms connected_natural_activation_counterexample
