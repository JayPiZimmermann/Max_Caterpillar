import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Falling

/-! Exact five-coordinate envelope after the sharp second-moment estimate. -/
set_option autoImplicit false
namespace MaxCaterpillar.OvernightConstants
open Frontier.RandomRestriction.GrowingMatching

theorem envelope_le (m K : ℕ) (hm : 501≤m) (hK : 0<K)
    (hupper : (K:ℝ)≤(m:ℝ)/12) :
    (2/7:ℝ)*((120:ℝ)/((m+5).descFactorial 4:ℝ)*((tailRate m K)^2)⁻¹*
      Real.exp (tailRate m K*(5*((m:ℝ)+4))))≤465/(K:ℝ)^2 := by
  have hmR : (501:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith only [hmR]
  have hK0 : (0:ℝ)<K := by exact_mod_cast hK
  have hdf : (m:ℝ)^4≤((m+5).descFactorial 4:ℝ) := by
    exact_mod_cast Parameters.tail_pow_le_descFactorial
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
  have hkr : (K:ℝ)/(m:ℝ)≤1/12 :=
    (div_le_iff hm0).mpr (by linarith only [hupper])
  have hmr : ((m:ℝ)+4)/((m:ℝ)-1)≤101/100 :=
    (div_le_iff hm1).mpr (by linarith only [hmR])
  have hmr0 : 0≤((m:ℝ)+4)/((m:ℝ)-1) := by positivity
  have hshift : tailRate m K*(5*((m:ℝ)+4))≤1/8 := by
    have hh := mul_le_mul hkr hmr hmr0 (by norm_num : (0:ℝ)≤1/12)
    calc
      _ = (35/24:ℝ)*((K:ℝ)/(m:ℝ)*(((m:ℝ)+4)/((m:ℝ)-1))) := by
        unfold tailRate
        field_simp [hm0.ne',hm1.ne']
        <;> ring
      _ ≤ (35/24:ℝ)*((1/12)*(101/100)) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ ≤ 1/8 := by norm_num
  have hexp : Real.exp (tailRate m K*(5*((m:ℝ)+4)))≤8/7 := by
    have hh := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0:ℝ)≤1/8) (by norm_num : (1/8:ℝ)<1)
    have hbound : Real.exp (1/8:ℝ)≤8/7 := by norm_num at hh ⊢; exact hh
    exact (Real.exp_le_exp.mpr hshift).trans hbound
  calc
    _ ≤ (2/7:ℝ)*(((69120/49:ℝ)/(K:ℝ)^2)*(8/7)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hbase hexp (Real.exp_pos _).le (by positivity)) (by norm_num)
    _ ≤ 465/(K:ℝ)^2 := by
      calc
        _ = (1105920/2401:ℝ)/(K:ℝ)^2 := by ring
        _ ≤ _ := div_le_div_of_le (sq_nonneg _) (by norm_num)

#print axioms envelope_le
end MaxCaterpillar.OvernightConstants
