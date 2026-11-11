import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.SamplingPoint

/-! Literal counts and finite sums on the variable-tail configuration fibers.
These identities expose the factorial-squared conditional normalization without
assuming a distribution or importing a Bernoulli probability conclusion. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Sampling
open BigOperators
variable {n : ℕ}

lemma rawConfig_card (S : Finset (Fin n)) :
    Fintype.card (RawConfig S)=(tailCount S).factorial^2 := by
  change Fintype.card (Equiv.Perm (Fin (tailCount S)) × Equiv.Perm (Fin (tailCount S)))=_
  simp only [Fintype.card_prod,Fintype.card_perm,Fintype.card_fin,pow_two]

lemma sum_rawConfig (S : Finset (Fin n)) (f : RawConfig S → ℝ) :
    (∑ p,f p)=∑ τ : Equiv.Perm (Fin (tailCount S)),
      ∑ ρ : Equiv.Perm (Fin (tailCount S)),f (τ,ρ) := Fintype.sum_prod_type

lemma average_rawConfig (S : Finset (Fin n)) (f : RawConfig S → ℝ) :
    (∑ p,f p)/(Fintype.card (RawConfig S):ℝ)=
      (∑ τ : Equiv.Perm (Fin (tailCount S)),∑ ρ : Equiv.Perm (Fin (tailCount S)),f (τ,ρ))/
        ((tailCount S).factorial:ℝ)^2 := by
  rw [sum_rawConfig,rawConfig_card,Nat.cast_pow]

lemma sum_samples (f : Sample n → ℝ) :
    (∑ ω,f ω)=∑ S : Finset (Fin n),∑ p : RawConfig S,f ⟨S,p⟩ := by
  rw [←Finset.univ_sigma_univ,Finset.sum_sigma]

lemma card_samples (n : ℕ) :
    Fintype.card (Sample n)=∑ S : Finset (Fin n),(tailCount S).factorial^2 := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro S _
  exact rawConfig_card S

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Sampling
