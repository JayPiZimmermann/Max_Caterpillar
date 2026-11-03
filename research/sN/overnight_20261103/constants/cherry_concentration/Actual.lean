import research.sN.overnight_20261103.constants.cherry_concentration.Concentration
import research.sN.overnight_20261103.constants.cherry_concentration.ExactMoment
import research.sN.overnight_20261103.constants.cherry_concentration.SecondMoment

/-! A closed bound for the literal bad isolated-gap event.
The exact mean, second moment and finite Chebyshev argument are all proved. -/
set_option autoImplicit false
namespace MaxCaterpillar.OvernightConstants.CherryConcentration
open BigOperators Frontier.RandomRestriction.GoodEvent
variable {m K : ℕ}

/-- At most one percent of actual uniform rank permutations have fewer than
K/2 isolated nonanchor gaps, even with K as large as m/8. -/
theorem badIsolated_fraction_le_one_percent (hm : 20000≤m) (hK : 36≤K)
    (hKm : 8*K≤m) :
    ((badIsolatedEvent m K).card:ℝ)/Fintype.card (Equiv.Perm (Fin m)) ≤ 1/100 := by
  have hmpos : 0<m := lt_of_lt_of_le (by decide : 0<20000) hm
  have hKle : K≤m := by linarith only [hKm]
  apply bad_fraction_le_of_moments hm hK hKm
  · exact rankAverage_selectedGapAdjacencies_eq ((by decide : 2≤20000).trans hm) hKle
  · have hs := Overnight.Constants.Cherry.rankAverage_adjacency_square_le hmpos hKle
    have hterm : 3*(K:ℝ)^3/(m:ℝ)^2 ≤ 4*(K:ℝ)^3/(m:ℝ)^2 :=
      div_le_div_of_le (sq_nonneg _) (by nlinarith only [pow_nonneg (Nat.cast_nonneg (α:=ℝ) K) 3])
    exact hs.trans (add_le_add_right (add_le_add_left hterm _) _)

/-- The practical cutoff floor(m/8) satisfies the closed one-percent bound. -/
theorem badIsolated_eighth_fraction_le_one_percent (hm : 20000≤m) :
    ((badIsolatedEvent m (m/8)).card:ℝ)/Fintype.card (Equiv.Perm (Fin m)) ≤ 1/100 := by
  apply badIsolated_fraction_le_one_percent hm
  · exact (Nat.le_div_iff_mul_le (by decide : 0<8)).mpr
      ((by decide : 36*8≤20000).trans hm)
  · simpa only [Nat.mul_comm] using Nat.div_mul_le_self m 8

#check @badIsolated_fraction_le_one_percent
#print axioms badIsolated_fraction_le_one_percent
#print axioms badIsolated_eighth_fraction_le_one_percent
end MaxCaterpillar.OvernightConstants.CherryConcentration
