import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.AffineLowerBound
import Mathlib.Data.Nat.Sqrt

/-! Arbitrary original first width, with a parameter chosen from that width.
The structural matching obstruction remains an explicit hypothesis. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.WidthTradeoff
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction AffineSkipExtension
open GrowingMatching GrowingMatching.AffineGeneralRows GrowingMatching.Bernoulli
variable {N h₁ h₂ : ℕ}

lemma half_pos (d : ℕ) (hd : 1 ≤ d)
    (hsize : 10000000000*d^2 ≤ N/2) : 0 < N/2 := by
  have hd2 : 1 ≤ d^2 := by nlinarith only [hd]
  nlinarith only [hsize,hd2]

def halfNeZero (N d : ℕ) (hd : 1 ≤ d)
    (hsize : 10000000000*d^2 ≤ N/2) : NeZero (N/2) :=
  ⟨Nat.ne_of_gt (half_pos d hd hsize)⟩

def originalNeZero (N d : ℕ) (hd : 1 ≤ d)
    (hsize : 10000000000*d^2 ≤ N/2) : NeZero N :=
  ⟨Nat.ne_of_gt ((half_pos d hd hsize).trans_le (Nat.div_le_self N 2))⟩

/-- The fourth-moment budget is derived directly from the original width.
No quadratic-width coefficient C is introduced. -/
theorem exists_affine_half_budgets (d : ℕ) (hd : 1 ≤ d)
    (hsize : 10000000000*d^2 ≤ N/2)
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := originalNeZero N d hd hsize;
      ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (hwidth : 81*h₁ ≤ 4*d^2*(N/2)^2) :
    letI := halfNeZero N d hd hsize;
    ∃ model : NormalizedNetwork (N/2) h₁ h₂,
      (∀ x, model.eval x = Maximum (N/2) x) ∧ model.TranslationNormalized ∧
      (nonBraidCount model : ℝ) ≤ (d : ℝ)^2*((N/2 : ℕ) : ℝ)^2 ∧
      (∑ j, ((rowSupport (model.A j)).card.descFactorial 4 : ℝ)) ≤
        (d : ℝ)^2*((N/2 : ℕ) : ℝ)^2 := by
  letI := originalNeZero N d hd hsize
  letI := halfNeZero N d hd hsize
  obtain ⟨S,hS,model,hmax,hnorm,hmoment,_⟩ :=
    exists_affine_half_model (n := N/2) net hnet (by linarith only [Nat.mul_div_le N 2])
  have hm : fourthMoment model ≤ d^2*(N/2)^2 := by
    have h := hmoment.trans hwidth
    nlinarith only [h]
  have hcount := (nonBraidCount_le_fourthMoment model).trans hm
  have hsum : (∑ j, (rowSupport (model.A j)).card.descFactorial 4) ≤
      d^2*(N/2)^2 := by
    exact (Finset.sum_le_sum (fun j _ => falling_four_le_large_support_cost _)).trans hm
  refine ⟨model,hmax,hnorm,?_,?_⟩
  · exact_mod_cast hcount
  · exact_mod_cast hsum

/-- Conditional width tradeoff for arbitrary original total first width.
Both hidden indices are the original ones; affine skips and biases are free.
Choose d on the scale sqrt(h₁)/(N/2). -/
theorem conditional_affine_width_tradeoff (d : ℕ) (hd : 1 ≤ d)
    (hsize : 10000000000*d^2 ≤ N/2)
    (H : LocalMatchingObstruction
      (Parameters.minimumArity (N/2) d) (Parameters.matchingOrder (N/2) d))
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := originalNeZero N d hd hsize;
      ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (hwidth : 81*h₁ ≤ 4*d^2*(N/2)^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/(8000*(d : ℝ))) ≤
      (h₂ : ℝ) := by
  letI := originalNeZero N d hd hsize
  letI := halfNeZero N d hd hsize
  obtain ⟨model,hmax,hnorm,hM,hL⟩ :=
    exists_affine_half_budgets d hd hsize net hnet hwidth
  exact conditional_sqrt_lower_bound hd hsize H model hnorm hmax hM hL

/-- A completely explicit integer parameter, with no square-root rounding
assumption left to the caller. -/
def widthParameter (n h : ℕ) : ℕ := Nat.sqrt (81*h/(4*n^2)) + 1

lemma widthParameter_pos (n h : ℕ) : 1 ≤ widthParameter n h := by
  unfold widthParameter
  exact Nat.succ_le_succ (Nat.zero_le _)

lemma widthParameter_budget (n h : ℕ) (hn : 0 < n) :
    81*h ≤ 4*(widthParameter n h)^2*n^2 := by
  have hden : 0 < 4*n^2 := by positivity
  have hs : 81*h/(4*n^2) < (widthParameter n h)^2 := by
    simpa only [widthParameter,Nat.succ_eq_add_one] using
      Nat.lt_succ_sqrt' (81*h/(4*n^2))
  have hh := (Nat.div_lt_iff_lt_mul hden).mp hs
  nlinarith only [hh]

/-- The first-width parameter is derived from the original width itself.
The remaining size condition permits widths of order N³, subject to the
explicit constants; the structural H premise is still unproved in general. -/
theorem conditional_affine_width_tradeoff_explicit
    (hsize : 10000000000*(widthParameter (N/2) h₁)^2 ≤ N/2)
    (H : LocalMatchingObstruction
      (Parameters.minimumArity (N/2) (widthParameter (N/2) h₁))
      (Parameters.matchingOrder (N/2) (widthParameter (N/2) h₁)))
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := originalNeZero N (widthParameter (N/2) h₁) (widthParameter_pos _ _) hsize;
      ∀ x, AffineSkipExtension.eval net x = Maximum N x) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/
      (8000*(widthParameter (N/2) h₁ : ℝ))) ≤ (h₂ : ℝ) :=
  conditional_affine_width_tradeoff _ (widthParameter_pos _ _) hsize H net hnet
    (widthParameter_budget _ _ (half_pos _ (widthParameter_pos _ _) hsize))

#check @conditional_affine_width_tradeoff_explicit
#print axioms exists_affine_half_budgets
#print axioms conditional_affine_width_tradeoff
#print axioms widthParameter_budget
#print axioms conditional_affine_width_tradeoff_explicit
end MaxCaterpillar.ExponentialPush.WidthTradeoff
