import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.GeneralRows

/-! The actual per-neuron cost for the integer general-row parameters. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters

theorem general_row_envelope (n d q : ℕ) (hd : 1≤d) (hq : 1≤q)
    (hn : 8000*d^2≤n) (hcube : 1000*d^2*q^3≤n) :
    perNeuronEnvelope (braidTail n q) (braidArity q) (generalRanks n d q) q ≤
      (400000*(d : ℝ)*(q : ℝ)^2/(n : ℝ))^q := by
  have hb := general_row_parameter_bounds n d q hd hq hn hcube
  have hm : 2≤braidTail n q := (by decide : 2≤400).trans hb.tail_four_hundred
  have hK : 0<generalRanks n d q := lt_of_lt_of_le (by decide : 0<4) hb.ranks_lower
  have hKu : 100*generalRanks n d q≤braidTail n q := by
    linarith only [hb.ranks_upper_weak]
  have hshape : braidTail n q+braidArity q+2≤3*braidTail n q := by
    rw [hb.total_eq]
    exact hb.total_add_two_le_three_tail
  have he := perNeuronEnvelope_le_four_sq_div_pow hm hK hb.matching_arity hKu hshape hb.arity_le_five_q
  have hn0 : (0 : ℝ)<n := by exact_mod_cast lt_of_lt_of_le (by decide : 0<8000) hb.total_lower
  have hK0 : (0 : ℝ)<generalRanks n d q := by exact_mod_cast hK
  have hkq : (braidArity q : ℝ)≤5*(q : ℝ) := by exact_mod_cast hb.arity_le_five_q
  have hksq : (braidArity q : ℝ)^2≤25*(q : ℝ)^2 := by
    calc
      _ ≤ (5*(q : ℝ))^2 := pow_le_pow_left (Nat.cast_nonneg _) hkq 2
      _ = _ := by ring
  have hNl : (n : ℝ)≤4000*(d : ℝ)*(generalRanks n d q : ℝ) := by exact_mod_cast hb.ranks_lower_total
  have hbase : 4*(braidArity q : ℝ)^2/(generalRanks n d q : ℝ)≤
      400000*(d : ℝ)*(q : ℝ)^2/(n : ℝ) := by
    apply (div_le_div_iff hK0 hn0).mpr
    calc
      _ ≤ (4*(braidArity q : ℝ)^2)*(4000*(d : ℝ)*(generalRanks n d q : ℝ)) :=
        mul_le_mul_of_nonneg_left hNl (by positivity)
      _ = (16000*(d : ℝ)*(generalRanks n d q : ℝ))*(braidArity q : ℝ)^2 := by ring
      _ ≤ (16000*(d : ℝ)*(generalRanks n d q : ℝ))*(25*(q : ℝ)^2) :=
        mul_le_mul_of_nonneg_left hksq (by positivity)
      _ = _ := by ring
  exact he.trans (pow_le_pow_left (by positivity) hbase q)

#print axioms general_row_envelope
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
