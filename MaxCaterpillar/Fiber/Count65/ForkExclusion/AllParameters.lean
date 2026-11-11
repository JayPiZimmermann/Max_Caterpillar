import MaxCaterpillar.Fiber.Count65.ForkExclusion.BelowOneSpurious
import MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner.Signed

/-! # Complete residual obstruction for every admissible inward fork -/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion

/-- Every admissible two-root inward fork requires four signed residual gates.
The symmetric endpoint is included and all coefficients are arbitrary reals. -/
theorem ResidualSystem.card_ge_four {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0<α) (hβ : 0<β)
    (hαβ : α+β=1) (hακ : α≤κ) (hβκ : β≤κ) (hκ : κ≠1)
    (h : d.Represents α β κ) : 4≤Fintype.card ι := by
  rcases lt_or_gt_of_ne hκ with hκ1 | hκ1
  · by_cases ha : α<κ
    · exact d.card_ge_four_low_of_alpha_lt hα hβ hαβ ha hβκ hκ1 h
    by_cases hb : β<κ
    · exact d.card_ge_four_low_of_beta_lt hα hβ hαβ hακ hb hκ1 h
    have hαe : α=κ := le_antisymm hακ (le_of_not_gt ha)
    have hβe : β=κ := le_antisymm hβκ (le_of_not_gt hb)
    have hκh : κ=(1/2:ℝ) := by linarith only [hαe,hβe,hαβ]
    have hαh : α=(1/2:ℝ) := hαe.trans hκh
    have hβh : β=(1/2:ℝ) := hβe.trans hκh
    rw [hαh,hβh,hκh] at h
    exact d.card_ge_four_corner h
  · exact d.card_ge_four_gt_one hα hβ hαβ hκ1 h

#print axioms ResidualSystem.card_ge_four
end MaxCaterpillar.Fiber.Count65.ForkExclusion
