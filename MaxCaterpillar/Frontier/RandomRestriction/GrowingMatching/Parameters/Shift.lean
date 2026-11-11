import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.TailEnvelope

/-! Explicit geometric-series exponential constants for the growing-arity envelope. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
variable {m k K q : ℕ}

theorem exp_one_seventh_le : Real.exp (1/7 : ℝ) ≤ 7/6 := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0:ℝ) ≤ 1/7) (by norm_num : (1/7:ℝ) < 1)
  norm_num at h ⊢
  exact h

/-- The shift costs at most 7k/800 under the actual sparse-rank condition. -/
theorem shift_le_seven_mul_arity (hm : 2 ≤ m) (hKupper : 100*K ≤ m)
    (hshape : m+k+2 ≤ 3*m) :
    tailRate m K * ((k:ℝ)*((m:ℝ)+(k:ℝ)-1)) ≤ 7*(k:ℝ)/800 := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith only [hmR]
  have hm1 : (0:ℝ) < (m:ℝ)-1 := by linarith only [hmR]
  have hupperR : (100:ℝ)*K ≤ m := by exact_mod_cast hKupper
  have hshapeR : (m:ℝ)+(k:ℝ)+2 ≤ 3*m := by exact_mod_cast hshape
  have hKr : (K:ℝ)/(m:ℝ) ≤ (1/100:ℝ) := by
    apply (div_le_iff hm0).mpr
    linarith only [hupperR]
  have hNr : ((m:ℝ)+(k:ℝ)-1)/((m:ℝ)-1) ≤ 3 := by
    apply (div_le_iff hm1).mpr
    linarith only [hshapeR]
  have hNr0 : (0:ℝ) ≤ ((m:ℝ)+(k:ℝ)-1)/((m:ℝ)-1) := by
    apply div_nonneg _ hm1.le
    have hk0 := Nat.cast_nonneg (α := ℝ) k
    linarith only [hmR,hk0]
  have hprod := mul_le_mul hKr hNr hNr0 (by norm_num : (0:ℝ) ≤ 1/100)
  have hcoef : (0:ℝ) ≤ 7*(k:ℝ)/24 :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) (by norm_num)
  calc
    tailRate m K * ((k:ℝ)*((m:ℝ)+(k:ℝ)-1)) =
        (7*(k:ℝ)/24)*(((K:ℝ)/(m:ℝ))*(((m:ℝ)+(k:ℝ)-1)/((m:ℝ)-1))) := by
      unfold tailRate
      field_simp [hm0.ne',hm1.ne']
      <;> ring
    _ ≤ (7*(k:ℝ)/24)*((1/100:ℝ)*3) := mul_le_mul_of_nonneg_left hprod hcoef
    _ = 7*(k:ℝ)/800 := by ring

/-- The shift contributes at most (7/6)^q; no asymptotic approximation is used. -/
theorem exp_shift_le (hm : 2 ≤ m) (hKupper : 100*K ≤ m)
    (hshape : m+k+2 ≤ 3*m) (hkq : k ≤ 5*q) :
    Real.exp (tailRate m K * ((k:ℝ)*((m:ℝ)+(k:ℝ)-1))) ≤ (7/6:ℝ)^q := by
  have hs := shift_le_seven_mul_arity hm hKupper hshape
  have hkqR : (k:ℝ) ≤ 5*(q:ℝ) := by exact_mod_cast hkq
  have hq0 := Nat.cast_nonneg (α := ℝ) q
  have hshift : tailRate m K * ((k:ℝ)*((m:ℝ)+(k:ℝ)-1)) ≤ (q:ℝ)/7 := by
    linarith only [hs,hkqR,hq0]
  calc
    _ ≤ Real.exp ((q:ℝ)/7) := Real.exp_le_exp.mpr hshift
    _ = (Real.exp (1/7:ℝ))^q := by
      rw [show (q:ℝ)/7 = (q:ℝ)*(1/7) by ring,Real.exp_nat_mul]
    _ ≤ (7/6:ℝ)^q := pow_le_pow_left (Real.exp_pos _).le exp_one_seventh_le q

#print axioms exp_shift_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
