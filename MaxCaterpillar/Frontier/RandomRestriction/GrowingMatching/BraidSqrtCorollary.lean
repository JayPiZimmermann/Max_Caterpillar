import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidCorollary
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Sqrt

/-! # Exact square-root-floor form of the conditional braid lower bound -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidCorollary
open Parameters

def braidSqrtDimension_neZero (n : ℕ) (hN : 160000 ≤ n) : NeZero n :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 160000) hN)⟩

/-- Integer-square-root specialization of the actual finite-q network theorem. -/
theorem conditional_braid_sqrt_lower_bound {n h₁ h₂ : ℕ} (hN : 160000 ≤ n)
    (H : LocalMatchingObstruction (braidArity (braidSqrtMatching n)) (braidSqrtMatching n))
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : letI := braidSqrtDimension_neZero n hN; ∀ x, net.eval x = Maximum n x)
    (hbraid : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card ≤ 2) :
    (23/25:ℝ)*4^(braidSqrtMatching n) ≤ (h₂:ℝ) := by
  have hq := braidSqrtMatching_bounds n hN
  exact conditional_braid_integer_q_lower_bound (braidSqrtMatching n) hq.1 hq.2
    H net hn hnet hbraid

/-- The literal real sqrt/floor expression in consequence (B). The only
unproved premise is the displayed local structural obstruction at that order. -/
theorem conditional_braid_sqrt_floor_lower_bound {n h₁ h₂ : ℕ} (hN : 160000 ≤ n)
    (H : LocalMatchingObstruction
      (braidArity (Nat.floor (Real.sqrt (n:ℝ)/400))) (Nat.floor (Real.sqrt (n:ℝ)/400)))
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : letI := braidSqrtDimension_neZero n hN; ∀ x, net.eval x = Maximum n x)
    (hbraid : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card ≤ 2) :
    (23/25:ℝ)*4^(Nat.floor (Real.sqrt (n:ℝ)/400)) ≤ (h₂:ℝ) := by
  have H' : LocalMatchingObstruction (braidArity (braidSqrtMatching n)) (braidSqrtMatching n) := by
    simpa only [braidSqrtMatching_eq_floor] using H
  simpa only [braidSqrtMatching_eq_floor] using
    conditional_braid_sqrt_lower_bound hN H' net hn hnet hbraid

#check @conditional_braid_sqrt_floor_lower_bound
#print axioms conditional_braid_sqrt_lower_bound
#print axioms conditional_braid_sqrt_floor_lower_bound
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidCorollary
