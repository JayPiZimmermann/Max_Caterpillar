import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Association
set_option autoImplicit false
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli

-- Exact expected type: weight_nonneg
example : ∀ {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) ,
    0 ≤ weight p S := @weight_nonneg
#check @weight_nonneg
#print axioms weight_nonneg

-- Exact expected type: weight_eq_pow_card
example : ∀ {n : ℕ} (p : ℝ) (S : Finset (Fin n)) ,
    weight p S = p ^ S.card * (1 - p) ^ (n - S.card) := @weight_eq_pow_card
#check @weight_eq_pow_card
#print axioms weight_eq_pow_card

-- Exact expected type: sum_prod_choice
example : ∀ {n : ℕ} (a b : Fin n → ℝ) ,
    (∑ S : Finset (Fin n), ∏ i : Fin n, if i ∈ S then a i else b i) =
      ∏ i : Fin n, (a i + b i) := @sum_prod_choice
#check @sum_prod_choice
#print axioms sum_prod_choice

-- Exact expected type: mass_univ
example : ∀ {n : ℕ} (p : ℝ) ,  mass p (Finset.univ : Finset (Finset (Fin n))) = 1 := @mass_univ
#check @mass_univ
#print axioms mass_univ

-- Exact expected type: mean_one
example : ∀ {n : ℕ} (p : ℝ) ,  mean p (fun _ : Finset (Fin n) => 1) = 1 := @mean_one
#check @mean_one
#print axioms mean_one

-- Exact expected type: mass_nonneg
example : ∀ {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Finset (Fin n))) ,  0 ≤ mass p E := @mass_nonneg
#check @mass_nonneg
#print axioms mass_nonneg

-- Exact expected type: weight_modular
example : ∀ {n : ℕ} (p : ℝ) (S T : Finset (Fin n)) ,
    weight p S * weight p T = weight p (S ∩ T) * weight p (S ∪ T) := @weight_modular
#check @weight_modular
#print axioms weight_modular

-- Exact expected type: mass_contains
example : ∀ {n : ℕ} (p : ℝ) (I : Finset (Fin n)) ,
    mass p (Finset.univ.filter fun S : Finset (Fin n) => I ⊆ S) = p ^ I.card := @mass_contains
#check @mass_contains
#print axioms mass_contains

-- Exact expected type: mass_empty
example : ∀ {n : ℕ} (p : ℝ) ,  mass p (∅ : Finset (Finset (Fin n))) = 0 := @mass_empty
#check @mass_empty
#print axioms mass_empty

-- Exact expected type: mass_compl
example : ∀ {n : ℕ} (p : ℝ) (E : Finset (Finset (Fin n))) ,
    mass p Eᶜ = 1 - mass p E := @mass_compl
#check @mass_compl
#print axioms mass_compl

-- Exact expected type: mass_mono
example : ∀ {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {D E : Finset (Finset (Fin n))} (hDE : D ⊆ E) ,  mass p D ≤ mass p E := @mass_mono
#check @mass_mono
#print axioms mass_mono

-- Exact expected type: mass_le_one
example : ∀ {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Finset (Fin n))) ,  mass p E ≤ 1 := @mass_le_one
#check @mass_le_one
#print axioms mass_le_one

-- Exact expected type: mass_avoids
example : ∀ {n : ℕ} (p : ℝ) (I : Finset (Fin n)) ,
    mass p (Finset.univ.filter fun S : Finset (Fin n) => ¬ I ⊆ S) = 1 - p ^ I.card := @mass_avoids
#check @mass_avoids
#print axioms mass_avoids

-- Exact expected type: mean_mul_ge
example : ∀ {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset (Fin n) → ℝ} (hf0 : ∀ S, 0 ≤ f S) (hg0 : ∀ S, 0 ≤ g S)
    (hf : Monotone f) (hg : Monotone g) ,
    mean p f * mean p g ≤ mean p (fun S => f S * g S) := @mean_mul_ge
#check @mean_mul_ge
#print axioms mean_mul_ge

-- Exact expected type: mean_mul_ge_antitone
example : ∀ {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset (Fin n) → ℝ} (hf0 : ∀ S, 0 ≤ f S) (hg0 : ∀ S, 0 ≤ g S)
    (hf : Antitone f) (hg : Antitone g) ,
    mean p f * mean p g ≤ mean p (fun S => f S * g S) := @mean_mul_ge_antitone
#check @mean_mul_ge_antitone
#print axioms mean_mul_ge_antitone

-- Exact expected type: mean_indicator
example : ∀ {n : ℕ} (p : ℝ) (D : Finset (Finset (Fin n))) ,
    mean p (fun S => if S ∈ D then 1 else 0) = mass p D := @mean_indicator
#check @mean_indicator
#print axioms mean_indicator

-- Exact expected type: mean_mul_indicator
example : ∀ {n : ℕ} (p : ℝ) (D : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → ℝ) ,
    mean p (fun S => f S * if S ∈ D then 1 else 0) = ∑ S in D, weight p S * f S := @mean_mul_indicator
#check @mean_mul_indicator
#print axioms mean_mul_indicator

-- Exact expected type: antitone_indicator_of_isLowerSet
example : ∀ {n : ℕ} (D : Finset (Finset (Fin n)))
    (hD : IsLowerSet (D : Set (Finset (Fin n)))) ,
    Antitone (fun S => if S ∈ D then (1 : ℝ) else 0) := @antitone_indicator_of_isLowerSet
#check @antitone_indicator_of_isLowerSet
#print axioms antitone_indicator_of_isLowerSet

-- Exact expected type: mass_mul_le_mass_inter
example : ∀ {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D E : Finset (Finset (Fin n)))
    (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hE : IsLowerSet (E : Set (Finset (Fin n)))) ,
    mass p D * mass p E ≤ mass p (D ∩ E) := @mass_mul_le_mass_inter
#check @mass_mul_le_mass_inter
#print axioms mass_mul_le_mass_inter

-- Exact expected type: condMean_le_mean
example : ∀ {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0 < mass p D) (f : Finset (Fin n) → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Monotone f) ,
    condMean p D f ≤ mean p f := @condMean_le_mean
#check @condMean_le_mean
#print axioms condMean_le_mean

-- Exact expected type: prod_mass_le_mass_all
example : ∀ {n : ℕ} {ι : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Finset ι) (E : ι → Finset (Finset (Fin n)))
    (hE : ∀ j ∈ J, IsLowerSet (E j : Set (Finset (Fin n)))) ,
    (∏ j in J, mass p (E j)) ≤
      mass p (Finset.univ.filter fun S : Finset (Fin n) => ∀ j ∈ J, S ∈ E j) := @prod_mass_le_mass_all
#check @prod_mass_le_mass_all
#print axioms prod_mass_le_mass_all

-- Exact expected type: condMean_contains_le
example : ∀ {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0 < mass p D) (I : Finset (Fin n)) ,
    condMean p D (fun S => if I ⊆ S then 1 else 0) ≤ p ^ I.card := @condMean_contains_le
#check @condMean_contains_le
#print axioms condMean_contains_le

example {n : ℕ} (p : ℝ) (S : Finset (Fin n)) : weight p S = (∏ i : Fin n, if i ∈ S then p else 1-p) := rfl
example {n : ℕ} (p : ℝ) (D : Finset (Finset (Fin n))) : mass p D = (∑ S in D, weight p S) := rfl
example {n : ℕ} (p : ℝ) (f : Finset (Fin n) → ℝ) : mean p f = (∑ S, weight p S * f S) := rfl
example {n : ℕ} (p : ℝ) (D : Finset (Finset (Fin n))) (f : Finset (Fin n) → ℝ) : condMean p D f = (mass p D)⁻¹ * (∑ S in D, weight p S * f S) := rfl
