import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.TailEnvelope

/-! # Falling-factorial cancellation in the actual growing-matching envelope

The denominator is bounded directly using the actual descending factorial.
No ratio or probability envelope is taken as a hypothesis. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters

/-- Every retained factor is at least the tail size when 2q<=k. -/
theorem tail_pow_le_descFactorial {m k q : ℕ} (hqk : 2*q ≤ k) :
    m^(2*q) ≤ (m+k).descFactorial (2*q) := by
  have hb : m ≤ m+k+1-2*q := Nat.le_sub_of_add_le (by linarith only [hqk])
  exact (Nat.pow_le_pow_left hb (2*q)).trans (Nat.pow_sub_le_descFactorial (m+k) (2*q))

/-- The genuine factorial ratio cancels the tail rate up to the stated
24/7 factor. The empty matching q=0 is included. -/
theorem falling_tail_envelope_le {m k K q : ℕ}
    (hm : 2 ≤ m) (hK : 0 < K) (hqk : 2*q ≤ k) :
    ((k.descFactorial (2*q) : ℝ) / ((m+k).descFactorial (2*q) : ℝ)) *
        ((tailRate m K)^q)⁻¹ ≤
      (24*(k : ℝ)^2/(7*(K : ℝ)))^q := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith only [hmR]
  have hmp : (0 : ℝ) < (m : ℝ)-1 := by linarith only [hmR]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hrate : 0 < tailRate m K := by
    exact div_pos (mul_pos (by norm_num) hKpos)
      (mul_pos (mul_pos (by norm_num) hmpos) hmp)
  have hCpos : (0 : ℝ) < 7*(K : ℝ)/24 :=
    div_pos (mul_pos (by norm_num) hKpos) (by norm_num)
  have hbase : 7*(K : ℝ)/24 ≤ (m : ℝ)^2 * tailRate m K := by
    have hratio : (1 : ℝ) ≤ (m : ℝ)/((m : ℝ)-1) :=
      (le_div_iff hmp).mpr (by linarith)
    calc
      7*(K : ℝ)/24 = (7*(K : ℝ)/24)*1 := (mul_one _).symm
      _ ≤ (7*(K : ℝ)/24)*((m : ℝ)/((m : ℝ)-1)) :=
        mul_le_mul_of_nonneg_left hratio hCpos.le
      _ = (m : ℝ)^2 * tailRate m K := by
        unfold tailRate
        field_simp [hmpos.ne',hmp.ne'] <;> ring
  have hlow : ((m : ℝ)^2)^q ≤ ((m+k).descFactorial (2*q) : ℝ) := by
    have hh : (m : ℝ)^(2*q) ≤ ((m+k).descFactorial (2*q) : ℝ) := by
      exact_mod_cast tail_pow_le_descFactorial (m := m) hqk
    simpa only [pow_mul] using hh
  have hden : (7*(K : ℝ)/24)^q ≤
      ((m+k).descFactorial (2*q) : ℝ) * (tailRate m K)^q := by
    calc
      (7*(K : ℝ)/24)^q ≤ ((m : ℝ)^2 * tailRate m K)^q :=
        pow_le_pow_left hCpos.le hbase q
      _ = ((m : ℝ)^2)^q * (tailRate m K)^q := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hlow (pow_nonneg hrate.le q)
  have hnum : (k.descFactorial (2*q) : ℝ) ≤ ((k : ℝ)^2)^q := by
    have hh : (k.descFactorial (2*q) : ℝ) ≤ (k : ℝ)^(2*q) := by
      exact_mod_cast Nat.descFactorial_le_pow k (2*q)
    simpa only [pow_mul] using hh
  calc
    ((k.descFactorial (2*q) : ℝ) / ((m+k).descFactorial (2*q) : ℝ)) *
        ((tailRate m K)^q)⁻¹ =
      (k.descFactorial (2*q) : ℝ) /
        (((m+k).descFactorial (2*q) : ℝ) * (tailRate m K)^q) := by
          simp only [div_eq_mul_inv,mul_inv]
          ring
    _ ≤ ((k : ℝ)^2)^q / (7*(K : ℝ)/24)^q :=
      div_le_div (pow_nonneg (sq_nonneg _) q) hnum (pow_pos hCpos q) hden
    _ = (24*(k : ℝ)^2/(7*(K : ℝ)))^q := by
      rw [← div_pow]
      congr 1
      field_simp [hKpos.ne'] <;> ring

#check @falling_tail_envelope_le
#print axioms tail_pow_le_descFactorial
#print axioms falling_tail_envelope_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
