import MaxCaterpillar.Frontier.RandomRestriction.ConfigurationsGeometry
import MaxCaterpillar.Frontier.RandomRestriction.BadFirstModel
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesProbability

/-! # The two elementary exceptional events on the actual product sample

The events are literal products with free coordinates. Their cardinal bounds
use no independence hypothesis and retain every original first-neuron index.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
open Configurations
variable {m : ℕ} {κ : Type*} [Fintype κ]

noncomputable def firstCoordinateEvent (B : Finset (FullPerm m)) :
    Finset (Configuration m) := by
  classical
  exact Finset.univ.filter fun ω => ω.1 ∈ B
noncomputable def rankCoordinateEvent (B : Finset (RankPerm m)) :
    Finset (Configuration m) := by
  classical
  exact Finset.univ.filter fun ω => ω.2.2 ∈ B

@[simp] lemma mem_firstCoordinateEvent (B : Finset (FullPerm m)) (ω : Configuration m) :
    ω ∈ firstCoordinateEvent B ↔ ω.1 ∈ B := by
  classical
  simp only [firstCoordinateEvent,Finset.mem_filter,Finset.mem_univ,true_and]
@[simp] lemma mem_rankCoordinateEvent (B : Finset (RankPerm m)) (ω : Configuration m) :
    ω ∈ rankCoordinateEvent B ↔ ω.2.2 ∈ B := by
  classical
  simp only [rankCoordinateEvent,Finset.mem_filter,Finset.mem_univ,true_and]

noncomputable def firstCoordinateEventEquiv (B : Finset (FullPerm m)) :
    ↥(firstCoordinateEvent B) ≃ ↥B × (TailPerm m × RankPerm m) where
  toFun ω := (⟨ω.val.1,(mem_firstCoordinateEvent B ω.val).mp ω.property⟩,ω.val.2)
  invFun p := ⟨(p.1.val,p.2),(mem_firstCoordinateEvent B _).mpr p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def rankCoordinateEventEquiv (B : Finset (RankPerm m)) :
    ↥(rankCoordinateEvent B) ≃ FullPerm m × (TailPerm m × ↥B) where
  toFun ω := (ω.val.1,(ω.val.2.1,⟨ω.val.2.2,(mem_rankCoordinateEvent B ω.val).mp ω.property⟩))
  invFun p := ⟨(p.1,(p.2.1,p.2.2.val)),(mem_rankCoordinateEvent B _).mpr p.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma firstCoordinateEvent_card (B : Finset (FullPerm m)) :
    (firstCoordinateEvent B).card=B.card*Fintype.card (TailPerm m × RankPerm m) := by
  calc
    _ = Fintype.card ↥(firstCoordinateEvent B) := (Fintype.card_coe _).symm
    _ = Fintype.card (↥B × (TailPerm m × RankPerm m)) :=
      Fintype.card_congr (firstCoordinateEventEquiv B)
    _ = _ := by rw [Fintype.card_prod,Fintype.card_coe]

lemma rankCoordinateEvent_card (B : Finset (RankPerm m)) :
    (rankCoordinateEvent B).card=Fintype.card (FullPerm m)*Fintype.card (TailPerm m)*B.card := by
  calc
    _ = Fintype.card ↥(rankCoordinateEvent B) := (Fintype.card_coe _).symm
    _ = Fintype.card (FullPerm m × (TailPerm m × ↥B)) :=
      Fintype.card_congr (rankCoordinateEventEquiv B)
    _ = _ := by rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_coe]; ring

noncomputable def badFirstConfigurations (T : κ → Finset (Fin (m+5))) :
    Finset (Configuration m) := firstCoordinateEvent (BadFirst.badFirstEvent T)

noncomputable def badIsolatedConfigurations (m K : ℕ) : Finset (Configuration m) :=
  rankCoordinateEvent (GoodEvent.badIsolatedEvent m K)

lemma selectedLabels_eq_selectedSet (σ : FullPerm m) :
    SelectedSetProbability.selectedLabels σ=selectedSet σ := by
  ext v
  simp only [SelectedSetProbability.mem_selectedLabels,selectedSet,
    Finset.mem_filter,Finset.mem_univ,true_and]

@[simp] lemma mem_badFirstConfigurations (T : κ → Finset (Fin (m+5)))
    (ω : Configuration m) : ω ∈ badFirstConfigurations T ↔
      ∃ j,3 ≤ (T j).card ∧ T j ⊆ selectedSet ω.1 := by
  classical
  simp only [badFirstConfigurations,mem_firstCoordinateEvent,
    BadFirst.mem_badFirstEvent,selectedLabels_eq_selectedSet]

@[simp] lemma mem_badIsolatedConfigurations (K : ℕ) (ω : Configuration m) :
    ω ∈ badIsolatedConfigurations m K ↔
      ((GoodEvent.isolatedGaps (GoodEvent.smallRankGaps ω.2.2 K)).card : ℝ)<(K : ℝ)/2 := by
  classical
  simp only [badIsolatedConfigurations,mem_rankCoordinateEvent,
    GoodEvent.mem_badIsolatedEvent]

lemma badFirstConfigurations_card_nat (T : κ → Finset (Fin (m+5)))
    (hbudget : 240*BadFirst.largeSupportCount T ≤ (m+5).descFactorial 3) :
    4*(badFirstConfigurations T).card ≤ Fintype.card (Configuration m) := by
  have hB := BadFirst.badFirstEvent_card_four_mul_le (Nat.le_add_left 5 m) T hbudget
  have h := Nat.mul_le_mul_right (Fintype.card (TailPerm m × RankPerm m)) hB
  simpa only [badFirstConfigurations,firstCoordinateEvent_card,
    Fintype.card_prod,Nat.mul_assoc] using h

/-- The first actual exceptional event occupies at most one quarter. -/
theorem badFirstConfigurations_card_le (T : κ → Finset (Fin (m+5)))
    (hbudget : 240*BadFirst.largeSupportCount T ≤ (m+5).descFactorial 3) :
    4*((badFirstConfigurations T).card : ℝ) ≤ (Fintype.card (Configuration m) : ℝ) := by
  exact_mod_cast badFirstConfigurations_card_nat T hbudget

/-- The isolated-gap event occupies at most eight percent of the complete
three-permutation product, with the other coordinates genuinely free. -/
theorem badIsolatedConfigurations_card_le (K : ℕ) (hm : 0<m) (hK : 4≤K)
    (hsmall : (K : ℝ)≤(m : ℝ)/100) :
    25*((badIsolatedConfigurations m K).card : ℝ) ≤
      2*(Fintype.card (Configuration m) : ℝ) := by
  have hsmallR : (100 : ℝ)*(K : ℝ)≤(m : ℝ) := by linarith only [hsmall]
  have hsmallN : 100*K≤m := by exact_mod_cast hsmallR
  have hKm : K≤m := by
    have hh : K≤100*K := by nlinarith only [Nat.zero_le K]
    exact hh.trans hsmallN
  have hfrac := GoodEvent.badIsolatedEvent_fraction_le_eight_percent hm hKm hK hsmallN
  have hR : (0 : ℝ)<Fintype.card (RankPerm m) := by
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card (RankPerm m))
  have hB : 25*((GoodEvent.badIsolatedEvent m K).card : ℝ) ≤
      2*(Fintype.card (RankPerm m) : ℝ) := by
    have hh := (div_le_iff hR).mp hfrac
    linarith only [hh]
  have hp := mul_le_mul_of_nonneg_left hB
    (mul_nonneg (Nat.cast_nonneg (Fintype.card (FullPerm m)))
      (Nat.cast_nonneg (Fintype.card (TailPerm m))) :
      (0 : ℝ)≤(Fintype.card (FullPerm m) : ℝ)*(Fintype.card (TailPerm m) : ℝ))
  simp only [badIsolatedConfigurations,rankCoordinateEvent_card,
    Fintype.card_prod,Nat.cast_mul]
  convert hp using 1 <;> ring

#print axioms badFirstConfigurations_card_le
#print axioms badIsolatedConfigurations_card_le
end MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
