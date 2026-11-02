import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Choose.Basic

/-! Literal finite choices for the Bernoulli conditional route; no estimates or
network/probability assertions are built into these definitions. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters

noncomputable def alpha (d : ℕ) : ℝ := 1/(1000*(d:ℝ))
noncomputable def delta (d : ℕ) : ℝ := 1/(1000*(d:ℝ)^2)
noncomputable def selectionProbability (n d : ℕ) : ℝ :=
  1/(1000*(d:ℝ)*Real.sqrt (n:ℝ))
noncomputable def bernoulliMean (n d : ℕ) : ℝ := Real.sqrt (n:ℝ)/(1000*(d:ℝ))
def rankCount (n d : ℕ) : ℕ := n/(1000*d^2)
noncomputable def matchingOrder (n d : ℕ) : ℕ := Nat.floor (bernoulliMean n d/8)
noncomputable def minimumArity (n d : ℕ) : ℕ := 4*matchingOrder n d+1
noncomputable def selectedCap (n d : ℕ) : ℕ := Nat.floor (2*bernoulliMean n d)
noncomputable def minimumTail (n d : ℕ) : ℕ := n-selectedCap n d
noncomputable def baseRate (n d : ℕ) : ℝ := 7*(rankCount n d:ℝ)/(24*(n:ℝ)^2)

noncomputable def supportBudget (n d : ℕ) (L : ℝ) : ℝ :=
  L*(rankCount n d:ℝ)^2 /
      ((1-(rankCount n d:ℝ)/(minimumTail n d:ℝ))*
        ((minimumTail n d).descFactorial 4:ℝ)) +
  L*selectionProbability n d*(rankCount n d:ℝ)^2 /
      ((minimumTail n d:ℝ)*(1-(rankCount n d:ℝ)/(minimumTail n d:ℝ))*
        ((minimumTail n d).descFactorial 3:ℝ)) +
  L*(selectionProbability n d)^2*(rankCount n d:ℝ) /
      (2*((minimumTail n d).descFactorial 2:ℝ))

noncomputable def neuronEnvelope (n d : ℕ) : ℝ :=
  ((selectionProbability n d)^2/baseRate n d)^(matchingOrder n d)*
    Real.exp (baseRate n d*(selectedCap n d:ℝ)*((n:ℝ)-1))

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
