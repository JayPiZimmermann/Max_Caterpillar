import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows.Half
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GeneralRows

/-! # Finite support budgets from an original quadratic total first width -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows
open BigOperators NormalizedNetwork ActualHalfRestriction
variable {N n h₁ h₂ : ℕ}

/-- The fixed integer parameter used by the raw quadratic-width wrapper. -/
def quadraticParameter (C : ℕ) : ℕ := 20*C

lemma quadraticParameter_pos (C : ℕ) (hC : 1≤C) : 1≤quadraticParameter C := by
  unfold quadraticParameter
  linarith only [hC]

lemma half_positive (N C : ℕ) (hC : 1≤C)
    (hsize : 8000*(quadraticParameter C)^2≤N/2) : 0<N/2 := by
  have hd := quadraticParameter_pos C hC
  have hd2 : 1≤(quadraticParameter C)^2 := by nlinarith only [hd]
  nlinarith only [hsize,hd2]

def halfDimension_neZero (N C : ℕ) (hC : 1≤C)
    (hsize : 8000*(quadraticParameter C)^2≤N/2) : NeZero (N/2) :=
  ⟨Nat.ne_of_gt (half_positive N C hC hsize)⟩

def originalDimension_neZero (N C : ℕ) (hC : 1≤C)
    (hsize : 8000*(quadraticParameter C)^2≤N/2) : NeZero N :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (half_positive N C hC hsize) (Nat.div_le_self N 2))⟩

/-- Both parities obey N≤3 floor(N/2) once the selected arity is positive.
The deliberately slack d=20C absorbs the exact fourth-moment constant. -/
theorem fourthMoment_le_quadratic_budget (C : ℕ) (hC : 1≤C)
    (hn : 0<N/2) (hwidth : h₁≤C*N^2) (model : NormalizedNetwork (N/2) h₁ h₂)
    (hbudget : 4*fourthMoment model≤81*h₁) :
    fourthMoment model≤(quadraticParameter C)^2*(N/2)^2 := by
  have hN : N≤3*(N/2) := by
    have he := Nat.mod_add_div N 2
    have hr := Nat.mod_lt N (by decide : 0<2)
    linarith only [he,hr,hn]
  have hN2 : N^2≤9*(N/2)^2 := by
    calc N^2≤(3*(N/2))^2 := Nat.pow_le_pow_left hN 2
         _=9*(N/2)^2 := by ring
  have hw : h₁≤9*C*(N/2)^2 := by
    calc h₁≤C*N^2 := hwidth
         _≤C*(9*(N/2)^2) := Nat.mul_le_mul_left C hN2
         _=9*C*(N/2)^2 := by ring
  have hC2 : C≤C^2 := by nlinarith only [hC]
  have hf : 729*C≤4*(quadraticParameter C)^2 := by
    unfold quadraticParameter
    nlinarith only [hC2,hC]
  have hh : 4*fourthMoment model≤4*((quadraticParameter C)^2*(N/2)^2) := by
    calc 4*fourthMoment model≤81*h₁ := hbudget
         _≤81*(9*C*(N/2)^2) := Nat.mul_le_mul_left 81 hw
         _=(729*C)*(N/2)^2 := by ring
         _≤(4*(quadraticParameter C)^2)*(N/2)^2 := Nat.mul_le_mul_right _ hf
         _=4*((quadraticParameter C)^2*(N/2)^2) := by ring
  linarith only [hh]

lemma nonBraidCount_le_fourthMoment (model : NormalizedNetwork n h₁ h₂) :
    nonBraidCount model≤fourthMoment model := by
  have h := moment_controls_count model
  linarith only [h,Nat.zero_le (nonBraidCount model)]

lemma falling_four_le_large_support_cost (r : ℕ) :
    r.descFactorial 4≤if 3≤r then r^4 else 0 := by
  by_cases hr : 3≤r
  · rw [if_pos hr]
    exact Nat.descFactorial_le_pow r 4
  · rw [if_neg hr,Nat.descFactorial_eq_zero_iff_lt.mpr
      (lt_trans (lt_of_not_ge hr) (by decide : 3<4))]

/-- These are the literal ALL-first-row statistics consumed by the actual
general-row theorem, including output-only first-layer terms. -/
theorem general_rows_budgets_of_fourthMoment (C : ℕ)
    (model : NormalizedNetwork n h₁ h₂)
    (hbudget : fourthMoment model≤(quadraticParameter C)^2*n^2) :
    (BadFirst.largeSupportCount (firstSupports (m:=n) (k:=0) model) : ℝ)≤
        (quadraticParameter C : ℝ)^2*(n : ℝ)^2 ∧
      (∑ j,((firstSupports (m:=n) (k:=0) model j).card.descFactorial 4 : ℝ))≤
        (quadraticParameter C : ℝ)^2*(n : ℝ)^2 := by
  constructor
  · have hcount := (nonBraidCount_le_fourthMoment model).trans hbudget
    change (nonBraidCount model : ℝ)≤_
    exact_mod_cast hcount
  · have hsum : (∑ j,(rowSupport (model.A j)).card.descFactorial 4)≤fourthMoment model :=
      Finset.sum_le_sum fun j _ => falling_four_le_large_support_cost _
    have hh := hsum.trans hbudget
    change (∑ j,((rowSupport (model.A j)).card.descFactorial 4 : ℝ))≤_
    exact_mod_cast hh

#check @fourthMoment_le_quadratic_budget
#print axioms fourthMoment_le_quadratic_budget
#print axioms general_rows_budgets_of_fourthMoment
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows
