import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.Floors
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.SmallFalling
import Mathlib.Data.Nat.Factorial.Cast

/-! # Scalar support-contamination estimates for the Bernoulli parameter choices

The denominators below are genuine descending factorials of the actual
minimum tail size. No probability or desired support-budget bound is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters

private theorem descFactorial_two_lower (m : ℕ) (hm : 12 ≤ m) :
    (m : ℝ)^2/2 ≤ (m.descFactorial 2 : ℝ) := by
  have hmR : (12 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Nat.cast_descFactorial_two]
  calc
    (m : ℝ)^2/2 = (m : ℝ)*((m : ℝ)/2) := by ring
    _ ≤ (m : ℝ)*((m : ℝ)-1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hmR]) (Nat.cast_nonneg _)

/-- The three literal terms of (G), bounded using actual factorials. -/
theorem generic_supportBudget_le (m n K : ℕ) (D δ a p L : ℝ)
    (hm : 12 ≤ m) (hn : n ≤ 2*m) (hK : 100*K ≤ m)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hp : 0 ≤ p)
    (hL0 : 0 ≤ L) (hL : L ≤ D*(n : ℝ)^2)
    (hKδ : (K : ℝ) ≤ δ*(n : ℝ)) (hp2 : p^2*(n : ℝ) = a^2) :
    L*(K : ℝ)^2 / ((1-(K : ℝ)/(m : ℝ))*(m.descFactorial 4 : ℝ)) +
    L*p*(K : ℝ)^2 / ((m : ℝ)*(1-(K : ℝ)/(m : ℝ))*(m.descFactorial 3 : ℝ)) +
    L*p^2*(K : ℝ) / (2*(m.descFactorial 2 : ℝ)) ≤
      128*D*δ^2 + 64*D*p*δ^2 + 4*D*a^2*δ := by
  have hmR : (12 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith only [hmR]
  have hnR : (n : ℝ) ≤ 2*(m : ℝ) := by exact_mod_cast hn
  have hKR : 100*(K : ℝ) ≤ m := by exact_mod_cast hK
  have hgap : (1/2 : ℝ) ≤ 1-(K : ℝ)/(m : ℝ) := by
    have hr : (K : ℝ)/(m : ℝ) ≤ 1/100 :=
      (div_le_iff hmpos).mpr (by linarith only [hKR])
    linarith only [hr]
  have hgap0 : 0 ≤ 1-(K : ℝ)/(m : ℝ) := le_trans (by norm_num) hgap
  have htwo := descFactorial_two_lower m hm
  have hthree := GrowingMatching.Parameters.descFactorial_three_lower m hm
  have hfour := GrowingMatching.Parameters.descFactorial_four_lower m hm
  have hdenA : (m : ℝ)^4/8 ≤
      (1-(K : ℝ)/(m : ℝ))*(m.descFactorial 4 : ℝ) := by
    calc
      (m : ℝ)^4/8 = (1/2)*((m : ℝ)^4/4) := by ring
      _ ≤ (1-(K : ℝ)/(m : ℝ))*((m : ℝ)^4/4) :=
        mul_le_mul_of_nonneg_right hgap (div_nonneg (pow_nonneg hmpos.le _) (by norm_num))
      _ ≤ _ := mul_le_mul_of_nonneg_left hfour hgap0
  have hdenB0 : (m : ℝ)^3/4 ≤
      (1-(K : ℝ)/(m : ℝ))*(m.descFactorial 3 : ℝ) := by
    calc
      (m : ℝ)^3/4 = (1/2)*((m : ℝ)^3/2) := by ring
      _ ≤ (1-(K : ℝ)/(m : ℝ))*((m : ℝ)^3/2) :=
        mul_le_mul_of_nonneg_right hgap (div_nonneg (pow_nonneg hmpos.le _) (by norm_num))
      _ ≤ _ := mul_le_mul_of_nonneg_left hthree hgap0
  have hdenB : (m : ℝ)^4/4 ≤
      (m : ℝ)*(1-(K : ℝ)/(m : ℝ))*(m.descFactorial 3 : ℝ) := by
    calc
      (m : ℝ)^4/4 = (m : ℝ)*((m : ℝ)^3/4) := by ring
      _ ≤ (m : ℝ)*((1-(K : ℝ)/(m : ℝ))*(m.descFactorial 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdenB0 hmpos.le
      _ = _ := by ring
  have hdenC : (m : ℝ)^2 ≤ 2*(m.descFactorial 2 : ℝ) := by
    calc
      (m : ℝ)^2 = 2*((m : ℝ)^2/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htwo (by norm_num)
  have hn4 : (n : ℝ)^4 ≤ 16*(m : ℝ)^4 := by
    calc
      (n : ℝ)^4 ≤ (2*(m : ℝ))^4 := pow_le_pow_left (Nat.cast_nonneg _) hnR _
      _ = _ := by ring
  have hn2 : (n : ℝ)^2 ≤ 4*(m : ℝ)^2 := by
    calc
      (n : ℝ)^2 ≤ (2*(m : ℝ))^2 := pow_le_pow_left (Nat.cast_nonneg _) hnR _
      _ = _ := by ring
  have hNK : L*(K : ℝ)^2 ≤ D*δ^2*(16*(m : ℝ)^4) := by
    calc
      L*(K : ℝ)^2 ≤ (D*(n : ℝ)^2)*(K : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hL (sq_nonneg _)
      _ ≤ (D*(n : ℝ)^2)*(δ*(n : ℝ))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left (Nat.cast_nonneg _) hKδ 2)
          (mul_nonneg hD (sq_nonneg _))
      _ = (D*δ^2)*(n : ℝ)^4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn4 (mul_nonneg hD (sq_nonneg _))
  have hNB : L*p*(K : ℝ)^2 ≤ D*p*δ^2*(16*(m : ℝ)^4) := by
    calc
      L*p*(K : ℝ)^2 = (L*(K : ℝ)^2)*p := by ring
      _ ≤ (D*δ^2*(16*(m : ℝ)^4))*p := mul_le_mul_of_nonneg_right hNK hp
      _ = _ := by ring
  have hNC : L*p^2*(K : ℝ) ≤ 4*D*a^2*δ*(m : ℝ)^2 := by
    calc
      L*p^2*(K : ℝ) ≤ (D*(n : ℝ)^2)*p^2*(K : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL (sq_nonneg _)) (Nat.cast_nonneg _)
      _ ≤ (D*(n : ℝ)^2)*p^2*(δ*(n : ℝ)) :=
        mul_le_mul_of_nonneg_left hKδ
          (mul_nonneg (mul_nonneg hD (sq_nonneg _)) (sq_nonneg _))
      _ = (D*δ*a^2)*(n : ℝ)^2 := by rw [show (D*(n : ℝ)^2)*p^2*(δ*(n : ℝ)) =
          (D*δ)*(p^2*(n : ℝ))*(n : ℝ)^2 by ring,hp2]
      _ ≤ (D*δ*a^2)*(4*(m : ℝ)^2) :=
        mul_le_mul_of_nonneg_left hn2 (mul_nonneg (mul_nonneg hD hδ) (sq_nonneg _))
      _ = _ := by ring
  have hA : L*(K : ℝ)^2 /
      ((1-(K : ℝ)/(m : ℝ))*(m.descFactorial 4 : ℝ)) ≤ 128*D*δ^2 := by
    calc
      _ ≤ (L*(K : ℝ)^2)/((m : ℝ)^4/8) :=
        div_le_div_of_le_left (mul_nonneg hL0 (sq_nonneg _))
          (div_pos (pow_pos hmpos _) (by norm_num)) hdenA
      _ ≤ (D*δ^2*(16*(m : ℝ)^4))/((m : ℝ)^4/8) :=
        div_le_div_of_le (div_nonneg (pow_nonneg hmpos.le _) (by norm_num)) hNK
      _ = _ := by field_simp [hmpos.ne'] <;> ring
  have hB : L*p*(K : ℝ)^2 /
      ((m : ℝ)*(1-(K : ℝ)/(m : ℝ))*(m.descFactorial 3 : ℝ)) ≤ 64*D*p*δ^2 := by
    calc
      _ ≤ (L*p*(K : ℝ)^2)/((m : ℝ)^4/4) :=
        div_le_div_of_le_left (mul_nonneg (mul_nonneg hL0 hp) (sq_nonneg _))
          (div_pos (pow_pos hmpos _) (by norm_num)) hdenB
      _ ≤ (D*p*δ^2*(16*(m : ℝ)^4))/((m : ℝ)^4/4) :=
        div_le_div_of_le (div_nonneg (pow_nonneg hmpos.le _) (by norm_num)) hNB
      _ = _ := by field_simp [hmpos.ne'] <;> ring
  have hC : L*p^2*(K : ℝ)/(2*(m.descFactorial 2 : ℝ)) ≤ 4*D*a^2*δ := by
    calc
      _ ≤ (L*p^2*(K : ℝ))/((m : ℝ)^2) :=
        div_le_div_of_le_left (mul_nonneg (mul_nonneg hL0 (sq_nonneg _)) (Nat.cast_nonneg _))
          (pow_pos hmpos _) hdenC
      _ ≤ (4*D*a^2*δ*(m : ℝ)^2)/((m : ℝ)^2) :=
        div_le_div_of_le (pow_nonneg hmpos.le _) hNC
      _ = _ := by field_simp [hmpos.ne'] <;> ring
  exact add_le_add (add_le_add hA hB) hC

/-- Literal parameter constants already leave a substantial margin below .001. -/
theorem support_constants_le (d : ℕ) (p : ℝ) (hd : 1 ≤ d)
    (hp : p ≤ 1) (hδ : delta d ≤ 1/1000) :
    128*(d : ℝ)^2*(delta d)^2 + 64*(d : ℝ)^2*p*(delta d)^2 +
      4*(d : ℝ)^2*(alpha d)^2*delta d ≤ 1/1000 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith only [hdR]
  have hDδ : (d : ℝ)^2*delta d = 1/1000 := by
    unfold delta
    field_simp [hdpos.ne'] <;> ring
  have hDa : (d : ℝ)^2*(alpha d)^2 = 1/1000000 := by
    unfold alpha
    field_simp [hdpos.ne'] <;> ring
  have hδsq : (d : ℝ)^2*(delta d)^2 ≤ 1/1000000 := by
    calc
      (d : ℝ)^2*(delta d)^2 = ((d : ℝ)^2*delta d)*delta d := by ring
      _ = (1/1000)*delta d := by rw [hDδ]
      _ ≤ (1/1000)*(1/1000) := mul_le_mul_of_nonneg_left hδ (by norm_num)
      _ = _ := by norm_num
  have hpsq : (d : ℝ)^2*p*(delta d)^2 ≤ 1/1000000 := by
    calc
      (d : ℝ)^2*p*(delta d)^2 = p*((d : ℝ)^2*(delta d)^2) := by ring
      _ ≤ 1*((d : ℝ)^2*(delta d)^2) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (d : ℝ)^2*(delta d)^2 := one_mul _
      _ ≤ _ := hδsq
  have hadelta : (d : ℝ)^2*(alpha d)^2*delta d ≤ 1/1000000000 := by
    calc
      (d : ℝ)^2*(alpha d)^2*delta d = (1/1000000)*delta d := by rw [hDa]
      _ ≤ (1/1000000)*(1/1000) := mul_le_mul_of_nonneg_left hδ (by norm_num)
      _ = _ := by norm_num
  calc
    128*(d : ℝ)^2*(delta d)^2 + 64*(d : ℝ)^2*p*(delta d)^2 +
        4*(d : ℝ)^2*(alpha d)^2*delta d =
      128*((d : ℝ)^2*(delta d)^2) + 64*((d : ℝ)^2*p*(delta d)^2) +
        4*((d : ℝ)^2*(alpha d)^2*delta d) := by ring
    _ ≤ 128*(1/1000000) + 64*(1/1000000) + 4*(1/1000000000) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hδsq (by norm_num))
        (mul_le_mul_of_nonneg_left hpsq (by norm_num)))
        (mul_le_mul_of_nonneg_left hadelta (by norm_num))
    _ ≤ 1/1000 := by norm_num

/-- The short-isolated-gap ratio uses only the literal tail and rank sizes. -/
theorem generic_shortQ_le (m n K : ℕ) (δ : ℝ) (hm : 0 < m) (hn : n ≤ 2*m)
    (hKδ : (K : ℝ) ≤ δ*(n : ℝ)) (hδ : 0 ≤ δ) :
    8*(K : ℝ)/(m : ℝ) ≤ 16*δ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (n : ℝ) ≤ 2*(m : ℝ) := by exact_mod_cast hn
  calc
    8*(K : ℝ)/(m : ℝ) ≤ 8*(δ*(n : ℝ))/(m : ℝ) :=
      div_le_div_of_le hmR.le (mul_le_mul_of_nonneg_left hKδ (by norm_num))
    _ ≤ 8*(δ*(2*(m : ℝ)))/(m : ℝ) :=
      div_le_div_of_le hmR.le (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hnR hδ) (by norm_num))
    _ = 16*δ := by field_simp [hmR.ne'] <;> ring

/-- Literal support-contamination budget, with every floor and square-root
side condition discharged by the actual symbolic parameter bounds. -/
theorem supportBudget_le {n d : ℕ} {L : ℝ}
    (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n)
    (hL0 : 0 ≤ L) (hL : L ≤ (d : ℝ)^2*(n : ℝ)^2) :
    supportBudget n d L ≤ 1/1000 := by
  have B := parameter_bounds n d hd hn
  have hgen := generic_supportBudget_le (minimumTail n d) n (rankCount n d)
    ((d : ℝ)^2) (delta d) (alpha d) (selectionProbability n d) L
    ((by decide : 12 ≤ 400).trans B.tail_lower400) B.total_le_twice_tail
    B.hundred_ranks_le_tail (sq_nonneg _) B.delta_pos.le B.probability_pos.le
    hL0 hL B.ranks_real_upper (probability_sq_mul_total n d B.n_pos hd)
  have hconst := support_constants_le d (selectionProbability n d) hd
    B.probability_le_one B.delta_upper
  simpa only [supportBudget] using hgen.trans hconst

/-- Uniform short-Q bound in the same actual parameter regime. -/
theorem shortQ_budget_le {n d : ℕ}
    (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    8*(rankCount n d : ℝ)/(minimumTail n d : ℝ) ≤ 16/1000 := by
  have B := parameter_bounds n d hd hn
  calc
    8*(rankCount n d : ℝ)/(minimumTail n d : ℝ) ≤ 16*delta d :=
      generic_shortQ_le (minimumTail n d) n (rankCount n d) (delta d)
        (lt_of_lt_of_le (by decide : 0 < 400) B.tail_lower400)
        B.total_le_twice_tail B.ranks_real_upper B.delta_pos.le
    _ ≤ 16*(1/1000) := mul_le_mul_of_nonneg_left B.delta_upper (by norm_num)
    _ = 16/1000 := by ring

#print axioms generic_supportBudget_le
#print axioms supportBudget_le
#print axioms shortQ_budget_le
#print axioms support_constants_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
