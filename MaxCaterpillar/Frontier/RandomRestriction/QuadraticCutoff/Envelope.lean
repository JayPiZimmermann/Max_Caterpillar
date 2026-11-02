import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Falling

/-! Exact five-variable cost at the larger rank cutoff used below. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff
open GrowingMatching

theorem envelope_le (m K : ℕ) (hm : 8≤m) (hK : 0<K)
    (hupper : (K:ℝ)≤(m:ℝ)/25) :
    (120:ℝ)/((m+5).descFactorial 4:ℝ)*((tailRate m K)^2)⁻¹*
      Real.exp (tailRate m K*(5*((m:ℝ)+4)))≤1600/(K:ℝ)^2 := by
  have hmR : (8:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith only [hmR]
  have hK0 : (0:ℝ)<K := by exact_mod_cast hK
  have hdf : (m:ℝ)^4≤((m+5).descFactorial 4:ℝ) := by
    exact_mod_cast GrowingMatching.Parameters.tail_pow_le_descFactorial
      (m:=m) (k:=5) (q:=2) (by decide : 2*2≤5)
  have hD : (0:ℝ)<((m+5).descFactorial 4:ℝ) :=
    lt_of_lt_of_le (pow_pos hm0 4) hdf
  have hsub : ((m:ℝ)-1)^2≤(m:ℝ)^2 :=
    pow_le_pow_left hm1.le (by linarith) 2
  have hprod : (m:ℝ)^2*((m:ℝ)-1)^2≤((m+5).descFactorial 4:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hsub (sq_nonneg (m:ℝ))
    nlinarith only [hh,hdf]
  have hratio : (m:ℝ)^2*((m:ℝ)-1)^2/((m+5).descFactorial 4:ℝ)≤1 :=
    (div_le_one hD).mpr hprod
  have hbase : (120:ℝ)/((m+5).descFactorial 4:ℝ)*((tailRate m K)^2)⁻¹≤
      (69120/49:ℝ)/(K:ℝ)^2 := by
    calc
      _ = ((69120/49:ℝ)/(K:ℝ)^2)*
          ((m:ℝ)^2*((m:ℝ)-1)^2/((m+5).descFactorial 4:ℝ)) := by
        unfold tailRate
        field_simp [hm0.ne',hm1.ne',hK0.ne',hD.ne']
        <;> ring
      _ ≤ ((69120/49:ℝ)/(K:ℝ)^2)*1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := mul_one _
  have hkr : (K:ℝ)/(m:ℝ)≤1/25 :=
    (div_le_iff hm0).mpr (by linarith only [hupper])
  have hmr : ((m:ℝ)+4)/((m:ℝ)-1)≤12/7 :=
    (div_le_iff hm1).mpr (by linarith only [hmR])
  have hmr0 : 0≤((m:ℝ)+4)/((m:ℝ)-1) := by positivity
  have hshift : tailRate m K*(5*((m:ℝ)+4))≤1/10 := by
    have hh := mul_le_mul hkr hmr hmr0 (by norm_num : (0:ℝ)≤1/25)
    calc
      _ = (35/24:ℝ)*((K:ℝ)/(m:ℝ)*(((m:ℝ)+4)/((m:ℝ)-1))) := by
        unfold tailRate
        field_simp [hm0.ne',hm1.ne']
        <;> ring
      _ ≤ (35/24:ℝ)*((1/25)*(12/7)) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = 1/10 := by norm_num
  have hexp : Real.exp (tailRate m K*(5*((m:ℝ)+4)))≤10/9 := by
    have hh := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0:ℝ)≤1/10) (by norm_num : (1/10:ℝ)<1)
    have hbound : Real.exp (1/10:ℝ)≤10/9 := by norm_num at hh ⊢; exact hh
    exact (Real.exp_le_exp.mpr hshift).trans hbound
  calc
    _ ≤ ((69120/49:ℝ)/(K:ℝ)^2)*(10/9) :=
      mul_le_mul hbase hexp (Real.exp_pos _).le (by positivity)
    _ ≤ 1600/(K:ℝ)^2 := by
      calc
        _ = (691200/441:ℝ)/(K:ℝ)^2 := by ring
        _ ≤ _ := div_le_div_of_le (sq_nonneg _) (by norm_num)

#print axioms envelope_le
end MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff
