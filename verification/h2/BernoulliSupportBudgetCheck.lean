import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.SupportBudget

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
variable {n d : ℕ} {L : ℝ}

example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n)
    (hL0 : 0 ≤ L) (hL : L ≤ (d : ℝ)^2*(n : ℝ)^2) :
    supportBudget n d L ≤ 1/1000 := supportBudget_le hd hn hL0 hL

example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    8*(rankCount n d : ℝ)/(minimumTail n d : ℝ) ≤ 16/1000 :=
  shortQ_budget_le hd hn

-- The factorials in the denominator are actual descending factorials.
example (m : ℕ) (hm : 400 ≤ m) :
    (m : ℝ)^4/4 ≤ (m.descFactorial 4 : ℝ) :=
  GrowingMatching.Parameters.descFactorial_four_lower m ((by decide : 12 ≤ 400).trans hm)
example (m : ℕ) (hm : 400 ≤ m) :
    (m : ℝ)^3/2 ≤ (m.descFactorial 3 : ℝ) :=
  GrowingMatching.Parameters.descFactorial_three_lower m ((by decide : 12 ≤ 400).trans hm)

#check @generic_supportBudget_le
#check @supportBudget_le
#check @shortQ_budget_le
#print axioms generic_supportBudget_le
#print axioms support_constants_le
#print axioms supportBudget_le
#print axioms shortQ_budget_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
