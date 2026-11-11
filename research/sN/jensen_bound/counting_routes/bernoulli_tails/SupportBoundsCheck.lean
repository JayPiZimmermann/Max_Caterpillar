import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.SupportBounds

set_option autoImplicit false
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli

example (n : ℕ) (κ : Type*) [Fintype κ] (p : ℝ)
    (hp0 : 0 ≤ p) (hpHalf : p ≤ 1/2) (T : κ → Finset (Fin n)) :
    Real.exp (-2 * (largeSupports T).card * p^3) ≤ mass p (noInternalEvent T) :=
  exp_neg_two_card_mul_cube_le_mass_noInternalEvent hp0 hpHalf T

example (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Finset (Finset (Fin n))) : mass p A - mass p Bᶜ ≤ mass p (A ∩ B) :=
  mass_inter_ge_sub_compl hp0 hp1 A B

example (n : ℕ) (κ : Type*) [Fintype κ] (p : ℝ)
    (hp0 : 0 ≤ p) (hpHalf : p ≤ 1/2) (T : κ → Finset (Fin n)) :
    Real.exp (-2 * (largeSupports T).card * p^3) - Real.exp (-((n : ℝ)*p)/3) ≤
      mass p (admissibleSets T ⌊2*((n : ℝ)*p)⌋₊) :=
  mass_admissibleSets_floor_two_mean_ge hp0 hpHalf T

example (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Finset (Finset (Fin n))) (hD : 0 < mass p D) (k : ℕ)
    (hk : (k : ℝ) ≤ 3*((n : ℝ)*p)/5) :
    condMean p D (fun S => if S.card < k then 1 else 0) ≤
      Real.exp (-3*((n : ℝ)*p)/40) / mass p D :=
  condMean_card_lt_le hp0 hp1 D hD k hk

example (n : ℕ) (κ : Type*) [Fintype κ] (p : ℝ)
    (hp0 : 0 ≤ p) (hpHalf : p ≤ 1/2) (T : κ → Finset (Fin n)) (k : ℕ)
    (hk : (k : ℝ) ≤ 3*((n : ℝ)*p)/5)
    (hden : 0 < Real.exp (-2 * (largeSupports T).card * p^3) -
      Real.exp (-((n : ℝ)*p)/3)) :
    condMean p (admissibleSets T ⌊2*((n : ℝ)*p)⌋₊)
      (fun S => if S.card < k then 1 else 0) ≤
      Real.exp (-3*((n : ℝ)*p)/40) /
        (Real.exp (-2 * (largeSupports T).card * p^3) - Real.exp (-((n : ℝ)*p)/3)) :=
  condMean_admissibleSets_card_lt_le hp0 hpHalf T k hk hden

#check @exp_neg_two_card_mul_cube_le_mass_noInternalEvent
#check @mass_inter_ge_sub_compl
#check @mass_admissibleSets_floor_two_mean_ge
#check @condMean_card_lt_le
#check @condMean_admissibleSets_card_lt_le
#print axioms exp_neg_two_card_mul_cube_le_mass_noInternalEvent
#print axioms mass_inter_ge_sub_compl
#print axioms mass_admissibleSets_floor_two_mean_ge
#print axioms condMean_card_lt_le
#print axioms condMean_admissibleSets_card_lt_le
