import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-! # Explicit per-role rates for actual tail permutations and gap ranks -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent

noncomputable def caseARate (m K : ℕ) : ℝ :=
  4*(K:ℝ)^2/((1-(K:ℝ)/(m:ℝ))*(m.descFactorial 4:ℝ))
noncomputable def caseBRate (m K : ℕ) : ℝ :=
  2*(K:ℝ)^2/((m:ℝ)*(1-(K:ℝ)/(m:ℝ))*(m.descFactorial 3:ℝ))
noncomputable def caseCRate (m K : ℕ) : ℝ :=
  2*(K:ℝ)/(m.descFactorial 2:ℝ)

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
