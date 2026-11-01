import research.sN.width_tradeoff.Frontier
import research.sN.width_tradeoff.AuditTent
import research.sN.width_tradeoff.LowerFirst
import research.sN.width_tradeoff.LowerTransverse
import research.sN.width_tradeoff.UpperMax5
import research.sN.width_tradeoff.UpperNineNetwork
import research.sN.frontierN.overnight_general_antipodal

set_option autoImplicit false

namespace MaxCaterpillar.WidthTradeoff

open Frontier

/-- Current unrestricted lower bounds checked in this research batch. -/
theorem maximum_five_lower {a b : ℕ} (net : Network 5 a b)
    (he : ∀ x, net.eval x = Maximum 5 x) : 7 ≤ a ∧ 4 ≤ b := by
  have hb := OvernightGeneral.network_second_width_half_plus_one net he
  exact ⟨first_width_ge_seven_max5 net he, by omega⟩

example : ∃ net : Network 5 10 6, (∀ x, net.eval x = Maximum 5 x) ∧
    net.HasRationalWeights ∧ net.HasZeroBiases := max_five_ten_six

example : ∃ net : Network 5 9 14, (∀ x, net.eval x = Maximum 5 x) ∧
    net.HasRationalWeights ∧ net.HasZeroBiases := P4.max_five_nine_fourteen

example {N a b : ℕ} [NeZero N] (hN : 4 ≤ N) (net : Network N a b)
    (he : ∀ x, net.eval x = Maximum N x) : N + 2 ≤ a :=
  first_width_ge_add_two hN net he

example {N a b : ℕ} [NeZero N] (net : Network N a b)
    (he : ∀ x, net.eval x = Maximum N x) : N + 2 ≤ 2 * b :=
  OvernightGeneral.network_second_width_half_plus_one net he

example : LeastPair (Maximum 3) 4 3 := maximum_three_leastPair
example : LeastPair (Maximum 4) 6 3 := maximum_four_leastPair

/-- The separate unrestricted minima are attained and obey the current
Lean bounds. They need not be attained by the same network. -/
theorem maximum_five_minima_bounds :
    ∃ a b c d, Feasible (Maximum 5) a b ∧ Feasible (Maximum 5) c d ∧
      (∀ p q, Feasible (Maximum 5) p q → a ≤ p ∧ d ≤ q) ∧
      7 ≤ a ∧ a ≤ 9 ∧ 4 ≤ d ∧ d ≤ 6 := by
  obtain ⟨net9, h9, _, _⟩ := P4.max_five_nine_fourteen
  obtain ⟨net10, h10, _, _⟩ := max_five_ten_six
  have h9' : Feasible (Maximum 5) 9 14 := ⟨net9, h9⟩
  have h10' : Feasible (Maximum 5) 10 6 := ⟨net10, h10⟩
  obtain ⟨a, b, c, d, hab, hcd, hmin⟩ := coordinate_minima ⟨9, 14, h9'⟩
  obtain ⟨na, ha⟩ := hab
  obtain ⟨nc, hc⟩ := hcd
  exact ⟨a, b, c, d, ⟨na, ha⟩, ⟨nc, hc⟩, hmin,
    (maximum_five_lower na ha).1, (hmin 9 14 h9').1,
    (maximum_five_lower nc hc).2, (hmin 10 6 h10').2⟩

/-- The two-point tent frontier is a strict tradeoff in the common
actual-network formulation, not just two incomparable constructions. -/
theorem tent_strictTradeoff :
    StrictTradeoff (fun x : Point 1 => WidthTradeoffAudit.tent (x 0)) := by
  obtain ⟨h12, h21, h11⟩ := WidthTradeoffAudit.tent_width_tradeoff
  exact ⟨1, 2, 2, 1, h12, h21, by decide, by decide, h11⟩

theorem tent_has_no_leastPair :
    ¬ ∃ a b, LeastPair (fun x : Point 1 => WidthTradeoffAudit.tent (x 0)) a b :=
  strictTradeoff_not_leastPair tent_strictTradeoff

#check @maximum_five_lower
#check @maximum_five_minima_bounds
#check @max_five_ten_six
#check @P4.max_five_nine_fourteen
#check @tent_strictTradeoff
#check @tent_has_no_leastPair
#print axioms maximum_five_lower
#print axioms maximum_five_minima_bounds
#print axioms max_five_ten_six
#print axioms P4.max_five_nine_fourteen
#print axioms tent_strictTradeoff
#print axioms tent_has_no_leastPair

end MaxCaterpillar.WidthTradeoff
