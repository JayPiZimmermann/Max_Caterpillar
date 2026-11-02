import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.Coverage

/-! Literal Bernoulli sqrt parameters, exact floors, support/error budgets,
exponential neuron envelope, and scalar conditional counting consequence. -/

namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters

instance minimumArity_neZero (n d : ℕ) : NeZero (minimumArity n d) :=
  ⟨Nat.succ_ne_zero (4*matchingOrder n d)⟩

theorem minimumArity_pos (n d : ℕ) : 0 < minimumArity n d :=
  Nat.succ_pos (4*matchingOrder n d)

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
