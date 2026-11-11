import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Tails

set_option autoImplicit false
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators

example (n : ℕ) (p t : ℝ) :
    mean p (fun S : Finset (Fin n) => Real.exp (t * S.card)) =
      (1 - p + p * Real.exp t) ^ n := mean_exp_card p t

example (n : ℕ) (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mean p (fun S : Finset (Fin n) => Real.exp (t * S.card)) ≤
      Real.exp ((n : ℝ) * p * (Real.exp t - 1)) := mean_exp_card_le p t hp0 hp1

example (n : ℕ) (p t a : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Finset (Fin n))) (hE : ∀ S ∈ E, a ≤ t * (S.card : ℝ)) :
    mass p E ≤ Real.exp ((n : ℝ) * p * (Real.exp t - 1) - a) :=
  mass_le_exp_markov p t a hp0 hp1 E hE

example : Real.exp (1/2 : ℝ) ≤ 5/3 := exp_half_le_five_thirds
example : Real.exp (-(1/2 : ℝ)) ≤ 5/8 := exp_neg_half_le_five_eighths

example (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mass p (Finset.univ.filter fun S : Finset (Fin n) =>
      2 * ((n : ℝ) * p) < (S.card : ℝ)) ≤ Real.exp (-((n : ℝ) * p) / 3) :=
  mass_card_gt_two_mean_le p hp0 hp1

example (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mass p (Finset.univ.filter fun S : Finset (Fin n) =>
      (S.card : ℝ) ≤ 3 * ((n : ℝ) * p) / 5) ≤
      Real.exp (-3 * ((n : ℝ) * p) / 40) :=
  mass_card_le_three_fifths_mean_le p hp0 hp1

example (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    Real.exp (-2*x) ≤ 1-x := exp_neg_two_mul_le_one_sub hx0 hx1

example (ι : Type*) (J : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ J, 0 ≤ x i) (hx1 : ∀ i ∈ J, x i ≤ 1/2) :
    Real.exp (-2 * ∑ i in J, x i) ≤ ∏ i in J, (1 - x i) :=
  exp_neg_two_sum_le_prod_one_sub J x hx0 hx1

#check @mean_exp_card
#check @mean_exp_card_le
#check @mass_le_exp_markov
#check @exp_half_le_five_thirds
#check @exp_neg_half_le_five_eighths
#check @mass_card_gt_two_mean_le
#check @mass_card_le_three_fifths_mean_le
#check @exp_neg_two_mul_le_one_sub
#check @exp_neg_two_sum_le_prod_one_sub
#print axioms mean_exp_card
#print axioms mean_exp_card_le
#print axioms mass_le_exp_markov
#print axioms exp_half_le_five_thirds
#print axioms exp_neg_half_le_five_eighths
#print axioms mass_card_gt_two_mean_le
#print axioms mass_card_le_three_fifths_mean_le
#print axioms exp_neg_two_mul_le_one_sub
#print axioms exp_neg_two_sum_le_prod_one_sub
