import MaxCaterpillar.Frontier.RandomRestriction.ConfigurationsGeometry
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventSubset

/-! Exact selected-set and actual base-tail complement facts for the literal
three-permutation experiment. No network or probability premise is required. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Configurations
open GoodEvent GoodEventDominance
variable {m : ℕ}

lemma selectedSet_eq_smallRankGaps (σ : FullPerm m) :
    selectedSet σ=GoodEvent.smallRankGaps σ 5 := rfl

lemma selectedSet_card (σ : FullPerm m) : (selectedSet σ).card=5 :=
  GoodEvent.card_smallRankGaps (Nat.le_add_left 5 m) σ

lemma baseTail_image_complement_selectedSet (σ : FullPerm m) :
    Finset.univ.image (baseTail σ)=
      (Finset.univ : Finset (Fin (m+5))) \ selectedSet σ := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    simp only [selectedSet,Finset.mem_filter,Finset.mem_univ,true_and]
    change ¬(σ (σ.symm (tailPosition m j))).val<5
    rw [Equiv.apply_symm_apply]
    change ¬j.val+5<5
    exact Nat.not_lt.mpr (Nat.le_add_left 5 j.val)
  · intro hv
    have hn := (Finset.mem_sdiff.mp hv).2
    rcases full_position_cases (σ v) with ⟨s,hs⟩ | ⟨j,hj⟩
    · apply False.elim
      apply hn
      simp only [selectedSet,Finset.mem_filter,Finset.mem_univ,true_and]
      rw [hs]
      exact s.isLt
    · refine Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩
      change σ.symm (tailPosition m j)=v
      rw [←hj,Equiv.symm_apply_apply]

#print axioms selectedSet_card
#print axioms baseTail_image_complement_selectedSet
end MaxCaterpillar.Frontier.RandomRestriction.Configurations
