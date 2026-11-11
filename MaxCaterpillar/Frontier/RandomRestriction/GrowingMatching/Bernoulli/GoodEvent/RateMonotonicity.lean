import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Rates
import Mathlib.Tactic

/-! # Uniform tail-size bounds for the actual role rates -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent

lemma descFactorial_mono_base {a b : ℕ} (hab : a≤b) (d : ℕ) :
    a.descFactorial d≤b.descFactorial d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.descFactorial_succ,Nat.descFactorial_succ]
    exact Nat.mul_le_mul (Nat.sub_le_sub_right hab d) ih

lemma descFactorial_pos_real {m d : ℕ} (hd : d≤m) : (0:ℝ)<m.descFactorial d := by
  have hn : m.descFactorial d≠0 := by
    intro hz
    exact (not_lt_of_ge hd) (Nat.descFactorial_eq_zero_iff_lt.mp hz)
  exact_mod_cast Nat.pos_of_ne_zero hn

lemma rankSlack_pos {m K : ℕ} (hm : 0<m) (hK : K<m) :
    (0:ℝ)<1-(K:ℝ)/(m:ℝ) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hKR : (K:ℝ)<m := by exact_mod_cast hK
  exact sub_pos.mpr ((div_lt_one hmR).mpr hKR)

lemma rankSlack_mono {m0 m K : ℕ} (h0 : 0<m0) (hm : m0≤m) :
    1-(K:ℝ)/(m0:ℝ)≤1-(K:ℝ)/(m:ℝ) := by
  have h0R : (0:ℝ)<m0 := by exact_mod_cast h0
  have hmR : (m0:ℝ)≤m := by exact_mod_cast hm
  have hd := div_le_div_of_le_left (Nat.cast_nonneg K : (0:ℝ)≤K) h0R hmR
  linarith only [hd]

lemma caseARate_nonneg {m K : ℕ} (hm : 4≤m) (hK : K<m) : 0≤caseARate m K := by
  unfold caseARate
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (rankSlack_pos (lt_of_lt_of_le (by decide : 0<4) hm) hK).le (Nat.cast_nonneg _))
lemma caseBRate_nonneg {m K : ℕ} (hm : 4≤m) (hK : K<m) : 0≤caseBRate m K := by
  unfold caseBRate
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (rankSlack_pos (lt_of_lt_of_le (by decide : 0<4) hm) hK).le) (Nat.cast_nonneg _))
lemma caseCRate_nonneg (m K : ℕ) : 0≤caseCRate m K := by
  unfold caseCRate
  positivity

/-- Weakening to a lower tail size retains the actual role-A upper rate. -/
theorem caseARate_le_of_tail_lower_bound {m0 m K : ℕ}
    (h0 : 4≤m0) (hm : m0≤m) (hK : K<m0) : caseARate m K≤caseARate m0 K := by
  have h0pos := lt_of_lt_of_le (by decide : 0<4) h0
  have hslack0 := rankSlack_pos h0pos hK
  have hslack := rankSlack_mono (K:=K) h0pos hm
  have hfac : (m0.descFactorial 4:ℝ)≤m.descFactorial 4 := by
    exact_mod_cast descFactorial_mono_base hm 4
  have hden : (1-(K:ℝ)/(m0:ℝ))*(m0.descFactorial 4:ℝ)≤
      (1-(K:ℝ)/(m:ℝ))*(m.descFactorial 4:ℝ) :=
    mul_le_mul hslack hfac (Nat.cast_nonneg _)
      (hslack0.le.trans hslack)
  exact div_le_div_of_le_left (mul_nonneg (by norm_num : (0:ℝ)≤4) (sq_nonneg _))
    (mul_pos hslack0 (descFactorial_pos_real h0)) hden

/-- The selected single-label rate is uniform after the same tail-size weakening. -/
theorem caseBRate_le_of_tail_lower_bound {m0 m K : ℕ}
    (h0 : 4≤m0) (hm : m0≤m) (hK : K<m0) : caseBRate m K≤caseBRate m0 K := by
  have h0pos := lt_of_lt_of_le (by decide : 0<4) h0
  have h0R : (0:ℝ)<m0 := by exact_mod_cast h0pos
  have hmR : (m0:ℝ)≤m := by exact_mod_cast hm
  have hslack0 := rankSlack_pos h0pos hK
  have hslack := rankSlack_mono (K:=K) h0pos hm
  have hfirst : (m0:ℝ)*(1-(K:ℝ)/(m0:ℝ))≤(m:ℝ)*(1-(K:ℝ)/(m:ℝ)) :=
    mul_le_mul hmR hslack hslack0.le ((h0R.le).trans hmR)
  have hfac : (m0.descFactorial 3:ℝ)≤m.descFactorial 3 := by
    exact_mod_cast descFactorial_mono_base hm 3
  have hden : (m0:ℝ)*(1-(K:ℝ)/(m0:ℝ))*(m0.descFactorial 3:ℝ)≤
      (m:ℝ)*(1-(K:ℝ)/(m:ℝ))*(m.descFactorial 3:ℝ) :=
    mul_le_mul hfirst hfac (Nat.cast_nonneg _)
      ((mul_nonneg h0R.le hslack0.le).trans hfirst)
  exact div_le_div_of_le_left (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg _))
    (mul_pos (mul_pos h0R hslack0) (descFactorial_pos_real ((by decide : 3≤4).trans h0))) hden

theorem caseCRate_le_of_tail_lower_bound {m0 m K : ℕ}
    (h0 : 4≤m0) (hm : m0≤m) : caseCRate m K≤caseCRate m0 K := by
  have hfac : (m0.descFactorial 2:ℝ)≤m.descFactorial 2 := by
    exact_mod_cast descFactorial_mono_base hm 2
  exact div_le_div_of_le_left (mul_nonneg (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg _))
    (descFactorial_pos_real ((by decide : 2≤4).trans h0)) hfac

#print axioms caseARate_le_of_tail_lower_bound
#print axioms caseBRate_le_of_tail_lower_bound
#print axioms caseCRate_le_of_tail_lower_bound
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
