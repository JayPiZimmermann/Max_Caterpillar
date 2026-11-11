import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.Exponential
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.SupportBudget

/-! Scalar assembly from explicit analytic budgets, followed by conditional
finite counting. This file supplies no unproved network or probability law. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
variable {n d : ℕ}

/-- The actual-model three error estimates can be supplied in their explicit
unrounded forms; all final numerical budgets are derived here. -/
theorem coverage_from_explicit_budgets (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n)
    (M L bsize bgood bshort : ℝ) (hM : M ≤ (d:ℝ)^2*(n:ℝ)^2)
    (hL0 : 0 ≤ L) (hL : L ≤ (d:ℝ)^2*(n:ℝ)^2)
    (hs : bsize ≤ Real.exp (-3*bernoulliMean n d/40) /
      (Real.exp (-2*M*(selectionProbability n d)^3)-Real.exp (-bernoulliMean n d/3)))
    (hg : bgood ≤ supportBudget n d L)
    (hq : bshort ≤ 8*(rankCount n d:ℝ)/(minimumTail n d:ℝ)) :
    (9/10:ℝ) ≤ 1-bsize-bgood-bshort :=
  generic_coverage bsize bgood bshort
    (hs.trans (conditioned_size_ratio_le hd hn M hM))
    (hg.trans (supportBudget_le hd hn hL0 hL))
    (hq.trans (shortQ_budget_le hd hn))

/-- Strong finite scalar consequence when the actual conditional union gives
coverage .9. In particular, there is no rare-event mass loss in this step. -/
theorem conditional_width_mean_bound (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n)
    (h₂ : ℕ) (hfinite : (9/10:ℝ) ≤ (h₂:ℝ)*neuronEnvelope n d) :
    (9/10:ℝ)*Real.exp (3*bernoulliMean n d/8) ≤ (h₂:ℝ) := by
  have hf : (9/10:ℝ) ≤ (h₂:ℝ)*Real.exp (-(3*bernoulliMean n d/8)) :=
    hfinite.trans (mul_le_mul_of_nonneg_left (neuronEnvelope_le hd hn) (Nat.cast_nonneg h₂))
  calc
    (9/10:ℝ)*Real.exp (3*bernoulliMean n d/8) ≤
        ((h₂:ℝ)*Real.exp (-(3*bernoulliMean n d/8)))*Real.exp (3*bernoulliMean n d/8) :=
      mul_le_mul_of_nonneg_right hf (Real.exp_pos _).le
    _ = (h₂:ℝ) := by rw [mul_assoc,←Real.exp_add]; simp

/-- The requested explicit sqrt bound, with prefactor one half. -/
theorem conditional_width_bound (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n)
    (h₂ : ℕ) (hfinite : (9/10:ℝ) ≤ (h₂:ℝ)*neuronEnvelope n d) :
    (1/2:ℝ)*Real.exp (3*Real.sqrt (n:ℝ)/(8000*(d:ℝ))) ≤ (h₂:ℝ) := by
  have heq : 3*Real.sqrt (n:ℝ)/(8000*(d:ℝ)) = 3*bernoulliMean n d/8 := by
    unfold bernoulliMean
    calc
      3*Real.sqrt (n:ℝ)/(8000*(d:ℝ)) =
          3*Real.sqrt (n:ℝ)/((1000*(d:ℝ))*8) := by congr 1; ring
      _ = (3*Real.sqrt (n:ℝ)/(1000*(d:ℝ)))/8 := (div_div _ _ _).symm
      _ = 3*(Real.sqrt (n:ℝ)/(1000*(d:ℝ)))/8 := by rw [mul_div_assoc]
  rw [heq]
  calc
    (1/2:ℝ)*Real.exp (3*bernoulliMean n d/8) ≤
        (9/10:ℝ)*Real.exp (3*bernoulliMean n d/8) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
    _ ≤ (h₂:ℝ) := conditional_width_mean_bound hd hn h₂ hfinite

#check @conditional_width_bound
#print axioms coverage_from_explicit_budgets
#print axioms conditional_width_mean_bound
#print axioms conditional_width_bound
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
