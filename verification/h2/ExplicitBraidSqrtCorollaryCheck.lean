import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidSqrtCorollary

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open Parameters

example (n : ℕ) (hN : 160000 ≤ n) :
    1 ≤ braidSqrtMatching n ∧ 160000*(braidSqrtMatching n)^2 ≤ n :=
  braidSqrtMatching_bounds n hN
example (n : ℕ) : braidSqrtMatching n = Nat.floor (Real.sqrt (n:ℝ)/400) :=
  braidSqrtMatching_eq_floor n
example {n h₁ h₂ : ℕ} [NeZero n] (hN : 160000 ≤ n)
    (H : LocalMatchingObstruction
      (braidArity (Nat.floor (Real.sqrt (n:ℝ)/400))) (Nat.floor (Real.sqrt (n:ℝ)/400)))
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x = Maximum n x)
    (hbraid : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card ≤ 2) :
    (23/25:ℝ)*4^(Nat.floor (Real.sqrt (n:ℝ)/400)) ≤ (h₂:ℝ) :=
  BraidCorollary.conditional_braid_sqrt_floor_lower_bound hN H net hn hnet hbraid

#check @BraidCorollary.conditional_braid_sqrt_floor_lower_bound
#print axioms braidSqrtMatching_bounds
#print axioms braidSqrtMatching_eq_floor
#print axioms BraidCorollary.conditional_braid_sqrt_floor_lower_bound
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
