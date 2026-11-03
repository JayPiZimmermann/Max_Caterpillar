import research.sN.overnight_20261103.h1_tradeoffs.WidthParameter

/-! A square-root dependence on the quadratic-width coefficient. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.WidthTradeoff
open Frontier Frontier.RandomRestriction AffineSkipExtension GrowingMatching
variable {N h₁ h₂ : ℕ}

/-- Integer ceiling of sqrt(C), with the harmless value one at C=0. -/
def sqrtCeiling (C : ℕ) : ℕ := Nat.sqrt (C-1) + 1

lemma sqrtCeiling_pos (C : ℕ) : 1 ≤ sqrtCeiling C :=
  Nat.succ_le_succ (Nat.zero_le _)

lemma le_sqrtCeiling_sq (C : ℕ) : C ≤ (sqrtCeiling C)^2 := by
  have h := Nat.lt_succ_sqrt' (C-1)
  simp only [Nat.succ_eq_add_one] at h
  unfold sqrtCeiling
  by_cases hC : C=0
  · simp only [hC,Nat.zero_le]
  · have hp : 1 ≤ C := Nat.one_le_iff_ne_zero.mpr hC
    calc C=(C-1)+1 := (Nat.sub_add_cancel hp).symm
         _ ≤ (Nat.sqrt (C-1)+1)^2 := Nat.succ_le_of_lt h

lemma quadratic_budget_sqrt (C s : ℕ) (hC : C ≤ s^2)
    (hn : 10 ≤ N/2) (hwidth : h₁ ≤ C*N^2) :
    81*h₁ ≤ 4*(10*s)^2*(N/2)^2 := by
  have hN : 10*N ≤ 21*(N/2) := by
    have he := Nat.mod_add_div N 2
    have hr := Nat.mod_lt N (by decide : 0<2)
    linarith only [he,hr,hn]
  have hN2 : 100*N^2 ≤ 441*(N/2)^2 := by
    have h := Nat.pow_le_pow_left hN 2
    nlinarith only [h]
  have hcoeff : 35721*C ≤ 40000*s^2 := by nlinarith only [hC]
  have hh : 100*(81*h₁) ≤ 100*(4*(10*s)^2*(N/2)^2) := by
    calc
      100*(81*h₁) ≤ 81*C*(100*N^2) := by nlinarith only [hwidth]
      _ ≤ 81*C*(441*(N/2)^2) := Nat.mul_le_mul_left _ hN2
      _ = (35721*C)*(N/2)^2 := by ring
      _ ≤ (40000*s^2)*(N/2)^2 := Nat.mul_le_mul_right _ hcoeff
      _ = 100*(4*(10*s)^2*(N/2)^2) := by ring
  nlinarith only [hh]

/-- For h₁≤C N² the exponent loses only sqrt(C), rather than C.
No braid assumption is imposed on the original first hidden layer. -/
theorem conditional_affine_sqrt_coefficient (C : ℕ)
    (hsize : 10000000000*(10*sqrtCeiling C)^2 ≤ N/2)
    (H : LocalMatchingObstruction
      (Bernoulli.Parameters.minimumArity (N/2) (10*sqrtCeiling C))
      (Bernoulli.Parameters.matchingOrder (N/2) (10*sqrtCeiling C)))
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := originalNeZero N (10*sqrtCeiling C) (by have h := sqrtCeiling_pos C; linarith only [h]) hsize;
      ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (hwidth : h₁ ≤ C*N^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/
      (80000*(sqrtCeiling C : ℝ))) ≤ (h₂ : ℝ) := by
  have hd : 1 ≤ 10*sqrtCeiling C := by
    have h := sqrtCeiling_pos C
    linarith only [h]
  have hn : 10 ≤ N/2 := by
    have hsq : 1 ≤ (10*sqrtCeiling C)^2 := by nlinarith only [hd]
    nlinarith only [hsq,hsize]
  have h := conditional_affine_width_tradeoff (10*sqrtCeiling C) hd hsize H net hnet
    (quadratic_budget_sqrt C (sqrtCeiling C) (le_sqrtCeiling_sq C) hn hwidth)
  have he : (8000 : ℝ)*(10*sqrtCeiling C : ℕ)=80000*(sqrtCeiling C : ℝ) := by
    push_cast
    ring
  simpa only [he] using h

#check @conditional_affine_sqrt_coefficient
#print axioms le_sqrtCeiling_sq
#print axioms quadratic_budget_sqrt
#print axioms conditional_affine_sqrt_coefficient
end MaxCaterpillar.ExponentialPush.WidthTradeoff
