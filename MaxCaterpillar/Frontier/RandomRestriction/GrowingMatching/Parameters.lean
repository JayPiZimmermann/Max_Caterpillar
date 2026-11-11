import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Falling
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Shift
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Floors

/-! # Explicit finite parameter bounds for the growing-matching envelope

The generic estimate is shared by braid and arbitrary-row conditional routes.
All ratio, exponential and floor estimates are proved here, not assumed as an
envelope premise. Structural matching hypotheses enter only later network corollaries.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
variable {m k K q : ℕ}

/-- Exactly the per-neuron factor in the actual finite transfer (T). -/
noncomputable def perNeuronEnvelope (m k K q : ℕ) : ℝ :=
  ((k.descFactorial (2*q):ℝ)/((m+k).descFactorial (2*q):ℝ))*
    ((tailRate m K)^q)⁻¹*
      Real.exp (tailRate m K*((k:ℝ)*((m:ℝ)+(k:ℝ)-1)))

/-- Generic coarsening before imposing either route's final size cutoff. -/
theorem perNeuronEnvelope_le_four_sq_div_pow
    (hm : 2 ≤ m) (hK : 0 < K) (hqk : 2*q ≤ k)
    (hKupper : 100*K ≤ m) (hshape : m+k+2 ≤ 3*m) (hkq : k ≤ 5*q) :
    perNeuronEnvelope m k K q ≤ (4*(k:ℝ)^2/(K:ℝ))^q := by
  have hfall := falling_tail_envelope_le hm hK hqk
  have hexp := exp_shift_le hm hKupper hshape hkq
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hb0 : (0:ℝ) ≤ 24*(k:ℝ)^2/(7*(K:ℝ)) :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (by norm_num) hKpos.le)
  have hbase : (24*(k:ℝ)^2/(7*(K:ℝ)))*(7/6:ℝ) = 4*(k:ℝ)^2/(K:ℝ) := by
    field_simp [hKpos.ne'] <;> ring
  calc
    perNeuronEnvelope m k K q ≤
        (24*(k:ℝ)^2/(7*(K:ℝ)))^q*(7/6:ℝ)^q :=
      mul_le_mul hfall hexp (Real.exp_pos _).le (pow_nonneg hb0 q)
    _ = ((24*(k:ℝ)^2/(7*(K:ℝ)))*(7/6:ℝ))^q := (mul_pow _ _ _).symm
    _ = (4*(k:ℝ)^2/(K:ℝ))^q := by rw [hbase]

/-- The integer braid cutoff makes the explicit base at most one quarter. -/
theorem perNeuronEnvelope_le_quarter_pow
    (hm : 2 ≤ m) (hK : 0 < K) (hqk : 2*q ≤ k)
    (hKupper : 100*K ≤ m) (hshape : m+k+2 ≤ 3*m) (hkq : k ≤ 5*q)
    (hsize : 160000*q^2 ≤ m+k) (hlower : m+k ≤ 400*K) :
    perNeuronEnvelope m k K q ≤ (1/4:ℝ)^q := by
  have hkqR : (k:ℝ) ≤ 5*(q:ℝ) := by exact_mod_cast hkq
  have hksq : (k:ℝ)^2 ≤ 25*(q:ℝ)^2 := by
    calc
      (k:ℝ)^2 ≤ (5*(q:ℝ))^2 := pow_le_pow_left (Nat.cast_nonneg k) hkqR 2
      _ = 25*(q:ℝ)^2 := by ring
  have hsizeR : (160000:ℝ)*(q:ℝ)^2 ≤ (m:ℝ)+(k:ℝ) := by exact_mod_cast hsize
  have hlowerR : (m:ℝ)+(k:ℝ) ≤ 400*(K:ℝ) := by exact_mod_cast hlower
  have hbaseScale : 16*(k:ℝ)^2 ≤ K := by linarith only [hksq,hsizeR,hlowerR]
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hbase : 4*(k:ℝ)^2/(K:ℝ) ≤ (1/4:ℝ) := by
    apply (div_le_iff hKpos).mpr
    linarith only [hbaseScale]
  exact (perNeuronEnvelope_le_four_sq_div_pow hm hK hqk hKupper hshape hkq).trans
    (pow_le_pow_left (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hKpos.le) hbase q)

/-- All scalar hypotheses follow from q>=1 and 160000q²<=n with the literal
integer choices k=4q+1,m=n-k,K=floor(m/100). -/
theorem braid_envelope_le (n q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) :
    perNeuronEnvelope (braidTail n q) (braidArity q) (braidRanks n q) q ≤ (1/4:ℝ)^q := by
  have h := braid_parameter_bounds n q hq hsize
  apply perNeuronEnvelope_le_quarter_pow
  · exact (by decide : 2 ≤ 400).trans h.tail_four_hundred
  · exact lt_of_lt_of_le (by decide : 0 < 4) h.ranks_lower
  · exact h.matching_arity
  · exact h.ranks_upper
  · rw [h.total_eq]
    exact h.total_add_two_le_three_tail
  · exact h.arity_le_five_q
  · rw [h.total_eq]
    exact hsize
  · rw [h.total_eq]
    exact h.ranks_lower_total

#check @perNeuronEnvelope_le_four_sq_div_pow
#check @braid_envelope_le
#print axioms perNeuronEnvelope_le_four_sq_div_pow
#print axioms braid_envelope_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
