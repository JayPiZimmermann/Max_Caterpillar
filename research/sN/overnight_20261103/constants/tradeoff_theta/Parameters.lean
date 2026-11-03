import Mathlib

/-! A concrete square-root-scaled cutoff, with all floor conditions proved. -/
set_option autoImplicit false
namespace MaxCaterpillar.OvernightConstants.TradeoffTheta

noncomputable def cutoff (m : ℕ) (C : ℝ) : ℕ := ⌊(m:ℝ)/(10*Real.sqrt C)⌋₊

theorem cutoff_bounds (m : ℕ) (C : ℝ) (hC : 1≤C) (hm : 20000*C≤(m:ℝ)) :
    50≤cutoff m C ∧ cutoff m C<m ∧
    (cutoff m C:ℝ)≤(m:ℝ)/10 ∧
    100*C*(cutoff m C:ℝ)^2≤(m:ℝ)^2 ∧
    (m:ℝ)^2≤101*C*(cutoff m C:ℝ)^2 := by
  have hC0 : 0≤C := by linarith only [hC]
  have hs : 0≤Real.sqrt C := Real.sqrt_nonneg C
  have hs1 : 1≤Real.sqrt C := Real.le_sqrt_of_sq_le (by nlinarith only [hC])
  have hs0 : 0<Real.sqrt C := by linarith only [hs1]
  have hsC : Real.sqrt C≤C := by
    have hh := mul_le_mul_of_nonneg_left hs1 hs
    nlinarith only [hh,Real.sq_sqrt hC0]
  have hmR : (20000:ℝ)≤m := by linarith only [hm,hC]
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hms : 20000*Real.sqrt C≤(m:ℝ) := by linarith only [hm,hsC]
  have hD : 0<10*Real.sqrt C := by positivity
  have hKu : (cutoff m C:ℝ)≤(m:ℝ)/(10*Real.sqrt C) :=
    Nat.floor_le (by positivity)
  have hK1000 : 1000≤cutoff m C := by
    apply Nat.le_floor
    apply (le_div_iff hD).mpr
    norm_num only [Nat.cast_ofNat]
    linarith only [hms,hs]
  have hK50 : 50≤cutoff m C := (by decide : 50≤1000).trans hK1000
  have hprod : 10*Real.sqrt C*(cutoff m C:ℝ)≤(m:ℝ) := by
    have hh := (le_div_iff hD).mp hKu
    nlinarith only [hh]
  have hprod0 : 0≤10*Real.sqrt C*(cutoff m C:ℝ) := by positivity
  have hKsmall : (cutoff m C:ℝ)≤(m:ℝ)/10 := by
    have hh := mul_le_mul_of_nonneg_right hs1 (Nat.cast_nonneg (α:=ℝ) (cutoff m C))
    linarith only [hprod,hh]
  have hKm : cutoff m C<m := by
    have hh : (cutoff m C:ℝ)<m := by linarith only [hKsmall,hm0]
    exact_mod_cast hh
  have hKsq : 100*C*(cutoff m C:ℝ)^2≤(m:ℝ)^2 := by
    have hh := mul_self_le_mul_self hprod0 hprod
    have he : (10*Real.sqrt C*(cutoff m C:ℝ))*(10*Real.sqrt C*(cutoff m C:ℝ))=
        100*C*(cutoff m C:ℝ)^2 := by
      calc
        _=100*(Real.sqrt C)^2*(cutoff m C:ℝ)^2 := by ring
        _=_ := by rw [Real.sq_sqrt hC0]
    rw [he] at hh
    simpa only [←sq] using hh
  have hKl : (m:ℝ)≤(1001/100:ℝ)*Real.sqrt C*(cutoff m C:ℝ) := by
    have hh := Nat.lt_floor_add_one ((m:ℝ)/(10*Real.sqrt C))
    change (m:ℝ)/(10*Real.sqrt C)<(cutoff m C:ℝ)+1 at hh
    have ht := (div_lt_iff hD).mp hh
    have hK1000R : (1000:ℝ)≤cutoff m C := by exact_mod_cast hK1000
    have hl := mul_le_mul_of_nonneg_left hK1000R hs
    nlinarith only [ht,hl]
  have hmsq : (m:ℝ)^2≤101*C*(cutoff m C:ℝ)^2 := by
    have hh := mul_self_le_mul_self hm0.le hKl
    have he : ((1001/100:ℝ)*Real.sqrt C*(cutoff m C:ℝ))*
        ((1001/100:ℝ)*Real.sqrt C*(cutoff m C:ℝ))=
        (1002001/10000:ℝ)*C*(cutoff m C:ℝ)^2 := by
      calc
        _=(1002001/10000:ℝ)*(Real.sqrt C)^2*(cutoff m C:ℝ)^2 := by ring
        _=_ := by rw [Real.sq_sqrt hC0]
    rw [he] at hh
    have hp : 0≤C*(cutoff m C:ℝ)^2 := mul_nonneg hC0 (sq_nonneg _)
    nlinarith only [hh,hp]
  exact ⟨hK50,hKm,hKsmall,hKsq,hmsq⟩

#print axioms cutoff_bounds
end MaxCaterpillar.OvernightConstants.TradeoffTheta
