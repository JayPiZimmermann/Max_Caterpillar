import MaxCaterpillar.Frontier.Main
import MaxCaterpillar.Frontier.GeneralN
import MaxCaterpillar.SmallN.Max5General4

/-! Exact-type audit. All conclusions refer to the actual arbitrary-bias Network. -/

namespace MaxCaterpillar.Frontier.WidthTradeoffAudit

theorem max3_exact {a b : ℕ} :
    (∃ net : Network 3 a b, ∀ x, net.eval x = Maximum 3 x) ↔ 4 ≤ a ∧ 3 ≤ b :=
  max3_widths_iff

theorem max4_exact {a b : ℕ} :
    (∃ net : Network 4 a b, ∀ x, net.eval x = Maximum 4 x) ↔ 6 ≤ a ∧ 3 ≤ b :=
  max4_widths_iff

theorem max5_first_lower {a b : ℕ} (net : Network 5 a b)
    (h : ∀ x, net.eval x = Maximum 5 x) : 6 ≤ a := by
  exact first_width_ge_succ net h

theorem max5_16_6 :
    ∃ net : Network 5 16 6,
      (∀ x, net.eval x = Maximum 5 x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases := by
  exact SmallN.Max5General4.max_network

#print axioms max3_exact
#print axioms max4_exact
#print axioms max5_first_lower
#print axioms max5_16_6

end MaxCaterpillar.Frontier.WidthTradeoffAudit
