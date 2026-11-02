import MaxCaterpillar.Frontier.RandomRestriction.ConfigurationsCounting
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventWeighted

/-! # Lift the literal frozen good-event count to actual configurations

Only a proved full-permutation bijection is used. The pulled-back event reads
exactly the effective full permutation and the original gap-rank permutation. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Configurations
open BigOperators
variable {m : ℕ} {κ : Type*} [Fintype κ]

noncomputable def feedingBadConfigurationsThree
    (T : κ → Finset (Fin (m+5))) (K : ℕ) : Finset (Configuration m) :=
  pullbackEvent (GoodEvent.feedingBadConfigurations T K)

lemma feedingBadConfigurationsThree_card (T : κ → Finset (Fin (m+5))) (K : ℕ) :
    (feedingBadConfigurationsThree T K).card=
      Fintype.card (TailPerm m)*(GoodEvent.feedingBadConfigurations T K).card :=
  pullbackEvent_card _

lemma feedingBadConfigurationsThree_fraction (T : κ → Finset (Fin (m+5))) (K : ℕ) :
    ((feedingBadConfigurationsThree T K).card:ℝ)/(Fintype.card (Configuration m):ℝ)=
      GoodEvent.feedingBadFraction T K := pullbackEvent_fraction _

/-- The literal integer feeding-event bound gains exactly the same free-tail
factor as the full sample space. -/
lemma feedingBadConfigurationsThree_card_mul (T : κ → Finset (Fin (m+5))) (K : ℕ)
    (hm : 400≤m) (hKlow : 4≤K) (hKhigh : (K:ℝ)≤(m:ℝ)/100) :
    (feedingBadConfigurationsThree T K).card*m^4 ≤
      4*(∑ j,(T j).card.descFactorial 4)*K^2*Fintype.card (Configuration m) := by
  have h := GoodEvent.feedingBadConfigurations_card_mul T K hm hKlow hKhigh
  rw [feedingBadConfigurationsThree_card,card_configuration]
  calc
    _ = Fintype.card (TailPerm m)*((GoodEvent.feedingBadConfigurations T K).card*m^4) := by ring
    _ ≤ Fintype.card (TailPerm m)*
        (4*(∑ j,(T j).card.descFactorial 4)*K^2*Fintype.card (LiteralConfiguration m)) :=
      Nat.mul_le_mul_left _ h
    _ = _ := by ring

/-- The usual moment budget makes the actual three-permutation bad event
at most one quarter of the complete configuration count. -/
lemma feedingBadConfigurationsThree_card_le_quarter
    (T : κ → Finset (Fin (m+5))) (K : ℕ)
    (hm : 400≤m) (hKlow : 4≤K) (hKhigh : (K:ℝ)≤(m:ℝ)/100)
    (hbudget : 16*(∑ j,((T j).card.descFactorial 4:ℝ))*(K:ℝ)^2≤(m:ℝ)^4) :
    4*((feedingBadConfigurationsThree T K).card:ℝ) ≤ (Fintype.card (Configuration m):ℝ) := by
  have hmR : (0:ℝ)<m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<400) hm)
  have hf : GoodEvent.feedingBadFraction T K≤(1/4:ℝ) := by
    apply (GoodEvent.feedingBadFraction_le T K hm hKlow hKhigh).trans
    apply (div_le_iff (pow_pos hmR 4)).mpr
    nlinarith only [hbudget]
  have hC : (0:ℝ)<Fintype.card (Configuration m) := by
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card (Configuration m))
  rw [←feedingBadConfigurationsThree_fraction] at hf
  have h := (div_le_iff hC).mp hf
  nlinarith only [h]

end MaxCaterpillar.Frontier.RandomRestriction.Configurations
