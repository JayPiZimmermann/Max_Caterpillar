import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.Floors
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.ExponentialBasic

/-! Literal Bernoulli envelope and conditioning-denominator estimates. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
variable {n d : ℕ}

private theorem alpha_sq_eq_delta_div (hd : 1 ≤ d) : (alpha d)^2 = delta d/1000 := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hd
  unfold alpha delta
  field_simp [hdpos.ne'] <;> ring

private theorem scaled_alpha_sq (hd : 1 ≤ d) : (d:ℝ)^2*(alpha d)^2 = (1/1000000:ℝ) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hd
  unfold alpha
  field_simp [hdpos.ne'] <;> ring

theorem baseRate_pos (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) : 0 < baseRate n d := by
  have h := parameter_bounds n d hd hn
  have hK : (0:ℝ) < rankCount n d := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) h.ranks_lower
  have hN : (0:ℝ) < n := by exact_mod_cast h.n_pos
  exact div_pos (mul_pos (by norm_num) hK) (mul_pos (by norm_num) (sq_pos_of_pos hN))

/-- Exact literal cancellation gives the small base 48/7000. -/
theorem probability_sq_div_rate_le (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    (selectionProbability n d)^2/baseRate n d ≤ (48/7000:ℝ) := by
  have h := parameter_bounds n d hd hn
  have hN : (0:ℝ) < n := by exact_mod_cast h.n_pos
  have hK : (0:ℝ) < rankCount n d := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) h.ranks_lower
  have hp2 := probability_sq_mul_total n d h.n_pos hd
  have hnum : (selectionProbability n d)^2*(24*(n:ℝ)^2) =
      24*(alpha d)^2*(n:ℝ) := by
    calc
      _ = 24*(((selectionProbability n d)^2*(n:ℝ))*(n:ℝ)) := by ring
      _ = _ := by rw [hp2]; ring
  calc
    (selectionProbability n d)^2/baseRate n d =
        ((selectionProbability n d)^2*(24*(n:ℝ)^2))/(7*(rankCount n d:ℝ)) := by
      unfold baseRate
      field_simp [hN.ne',hK.ne'] <;> ring
    _ = (24*(alpha d)^2*(n:ℝ))/(7*(rankCount n d:ℝ)) := by rw [hnum]
    _ ≤ (48/7000:ℝ) := by
      apply (div_le_iff (mul_pos (by norm_num : (0:ℝ) < 7) hK)).mpr
      rw [alpha_sq_eq_delta_div hd]
      have hl := h.ranks_real_lower
      linarith only [hl]

/-- The literal cap and rank choices give a shift at most μ/1000. -/
theorem rate_shift_le (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    baseRate n d*(selectedCap n d:ℝ)*((n:ℝ)-1) ≤ bernoulliMean n d/1000 := by
  have h := parameter_bounds n d hd hn
  have hN : (0:ℝ) < n := by exact_mod_cast h.n_pos
  have hN1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt h.n_pos
  have hμ0 : 0 ≤ bernoulliMean n d := (by norm_num : (0:ℝ) ≤ 100).trans h.mean_lower
  have hc0 : 0 ≤ 7*delta d/(24*(n:ℝ)) :=
    div_nonneg (mul_nonneg (by norm_num) h.delta_pos.le)
      (mul_nonneg (by norm_num) hN.le)
  have hr : baseRate n d ≤ 7*delta d/(24*(n:ℝ)) := by
    calc
      baseRate n d = (7/(24*(n:ℝ)^2))*(rankCount n d:ℝ) := by unfold baseRate; ring
      _ ≤ (7/(24*(n:ℝ)^2))*(delta d*(n:ℝ)) :=
        mul_le_mul_of_nonneg_left h.ranks_real_upper (by positivity)
      _ = _ := by field_simp [hN.ne'] <;> ring
  have hnminus : (0:ℝ) ≤ (n:ℝ)-1 := by linarith only [hN1]
  have hprod : (selectedCap n d:ℝ)*((n:ℝ)-1) ≤
      (2*bernoulliMean n d)*(n:ℝ) :=
    mul_le_mul h.cap_upper (by linarith : (n:ℝ)-1 ≤ (n:ℝ)) hnminus
      (mul_nonneg (by norm_num) hμ0)
  have hp0 : (0:ℝ) ≤ (selectedCap n d:ℝ)*((n:ℝ)-1) :=
    mul_nonneg (Nat.cast_nonneg _) hnminus
  have hdμ := mul_le_mul_of_nonneg_right h.delta_upper hμ0
  calc
    baseRate n d*(selectedCap n d:ℝ)*((n:ℝ)-1) =
        baseRate n d*((selectedCap n d:ℝ)*((n:ℝ)-1)) := by ring
    _ ≤ (7*delta d/(24*(n:ℝ)))*((2*bernoulliMean n d)*(n:ℝ)) :=
      mul_le_mul hr hprod hp0 hc0
    _ = 7*delta d*bernoulliMean n d/12 := by field_simp [hN.ne'] <;> ring
    _ ≤ 7*(1/1000:ℝ)*bernoulliMean n d/12 := by linarith only [hdμ]
    _ ≤ bernoulliMean n d/1000 := by linarith only [hμ0]

/-- Strong literal envelope, with the harmless margin retained. -/
theorem neuronEnvelope_le_strong (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    neuronEnvelope n d ≤ Real.exp (-((7/18:ℝ)-1/1000)*bernoulliMean n d) := by
  have h := parameter_bounds n d hd hn
  have hb0 : 0 ≤ (selectionProbability n d)^2/baseRate n d :=
    div_nonneg (sq_nonneg _) (baseRate_pos hd hn).le
  have hb : (selectionProbability n d)^2/baseRate n d ≤ (1/128:ℝ) :=
    (probability_sq_div_rate_le hd hn).trans (by norm_num)
  exact generic_envelope_strong (bernoulliMean n d) _ _ (matchingOrder n d)
    hb0 hb h.order_lower (rate_shift_le hd hn)

theorem neuronEnvelope_le (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    neuronEnvelope n d ≤ Real.exp (-(3*bernoulliMean n d/8)) := by
  apply (neuronEnvelope_le_strong hd hn).trans
  have h := parameter_bounds n d hd hn
  have hμ0 : 0 ≤ bernoulliMean n d := (by norm_num : (0:ℝ) ≤ 100).trans h.mean_lower
  exact Real.exp_le_exp.mpr (by linarith only [hμ0])

/-- The noninternal mass exponent is uniformly at most 2e-6 μ. -/
theorem noInternalExponent_le (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n)
    (M : ℝ) (hM : M ≤ (d:ℝ)^2*(n:ℝ)^2) :
    2*M*(selectionProbability n d)^3 ≤ (2/1000000:ℝ)*bernoulliMean n d := by
  have h := parameter_bounds n d hd hn
  have hp2 := probability_sq_mul_total n d h.n_pos hd
  have hp1 := probability_mul_total n d h.n_pos hd
  have hm := mul_le_mul_of_nonneg_right hM (pow_nonneg h.probability_pos.le 3)
  calc
    2*M*(selectionProbability n d)^3 = 2*(M*(selectionProbability n d)^3) := by ring
    _ ≤ 2*((d:ℝ)^2*(n:ℝ)^2*(selectionProbability n d)^3) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = 2*((d:ℝ)^2*((selectionProbability n d)^2*(n:ℝ))*
        (selectionProbability n d*(n:ℝ))) := by ring
    _ = (2/1000000:ℝ)*bernoulliMean n d := by rw [hp2,hp1,scaled_alpha_sq hd]; ring

/-- The actual support-bound denominator is positive and pays at most half
of exp(-2e-6 μ), even with the weaker upper-tail exponent μ/6. -/
theorem admissible_denominator_lower (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n)
    (M : ℝ) (hM : M ≤ (d:ℝ)^2*(n:ℝ)^2) :
    (1/2:ℝ)*Real.exp (-(2/1000000:ℝ)*bernoulliMean n d) ≤
      Real.exp (-2*M*(selectionProbability n d)^3)-Real.exp (-bernoulliMean n d/3) := by
  have h := parameter_bounds n d hd hn
  have he : Real.exp (-(2/1000000:ℝ)*bernoulliMean n d) ≤
      Real.exp (-2*M*(selectionProbability n d)^3) := by
    apply Real.exp_le_exp.mpr
    have hm := noInternalExponent_le hd hn M hM
    linarith only [hm]
  have hu : Real.exp (-bernoulliMean n d/3) ≤ Real.exp (-bernoulliMean n d/6) := by
    apply Real.exp_le_exp.mpr
    linarith only [h.mean_lower]
  exact (generic_conditioning_mass_lower (bernoulliMean n d) h.mean_lower).trans
    (sub_le_sub he hu)

theorem admissible_denominator_pos (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n)
    (M : ℝ) (hM : M ≤ (d:ℝ)^2*(n:ℝ)^2) :
    0 < Real.exp (-2*M*(selectionProbability n d)^3)-Real.exp (-bernoulliMean n d/3) :=
  lt_of_lt_of_le (mul_pos (by norm_num : (0:ℝ) < 1/2) (Real.exp_pos _))
    (admissible_denominator_lower hd hn M hM)

theorem conditioned_size_ratio_le (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n)
    (M : ℝ) (hM : M ≤ (d:ℝ)^2*(n:ℝ)^2) :
    Real.exp (-3*bernoulliMean n d/40) /
      (Real.exp (-2*M*(selectionProbability n d)^3)-Real.exp (-bernoulliMean n d/3)) ≤
        (1/100:ℝ) :=
  generic_conditioned_size_ratio _ _ (parameter_bounds n d hd hn).mean_lower
    (admissible_denominator_lower hd hn M hM)

#print axioms neuronEnvelope_le
#print axioms conditioned_size_ratio_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
