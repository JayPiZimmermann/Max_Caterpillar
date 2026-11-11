import research.sN.overnight_20261103.constants.FallingHalfModel

/-! A single sharp half restriction controls both genuinely non-braid row
count and the fourth falling support moment. -/
set_option autoImplicit false
namespace MaxCaterpillar.Overnight.Constants.FallingHalf
open BigOperators WeightedRestriction Frontier Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction

def jointCost (s : ℕ) : ℕ := if 3≤s then max 105 (2*s.descFactorial 4) else 0

@[simp] theorem jointCost_zero : jointCost 0=0 := by norm_num [jointCost]

theorem jointCost_decay (s : ℕ) : 8*jointCost s≤105*2^s := by
  by_cases hs : 3≤s
  · rw [jointCost, if_pos hs]
    have hsmall : 8*105≤105*2^s := by
      have hh := Nat.pow_le_pow_right (by decide : 1≤2) hs
      norm_num at hh
      linarith only [hh]
    rcases le_total 105 (2*s.descFactorial 4) with h|h
    · rw [max_eq_right h]
      have hh := falling_four_decay s
      linarith only [hh]
    · rw [max_eq_left h]
      exact hsmall
  · simp [jointCost, hs]

theorem falling_le_jointCost (s : ℕ) : 2*s.descFactorial 4≤jointCost s := by
  by_cases hs : 3≤s
  · rw [jointCost, if_pos hs]
    exact le_max_right _ _
  · have hz : s.descFactorial 4=0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (lt_trans (Nat.lt_of_not_ge hs) (by decide))
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _

theorem count_le_jointCost (s : ℕ) : (if 3≤s then 105 else 0)≤jointCost s := by
  unfold jointCost
  split_ifs with hs
  · exact le_max_left _ _
  · exact Nat.zero_le _

theorem paired_joint_restriction {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (T : κ → Finset (ι×Bool)) :
    ∃ U : Finset (ι×Bool), U.card=Fintype.card ι ∧
      8*(∑ j, if T j⊆U then jointCost (T j).card else 0)≤105*Fintype.card κ := by
  classical
  obtain ⟨f, hf⟩ := exists_selector_cost T jointCost 8 105 jointCost_decay
  exact ⟨selected f, selected_card f, by simpa only [subset_selected] using hf⟩

theorem half_joint_restriction {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ]
    (n : ℕ) (hα : Fintype.card α=2*n) (T : κ → Finset α) :
    ∃ U : Finset α, U.card=n ∧
      8*(∑ j, if T j⊆U then jointCost (T j).card else 0)≤105*Fintype.card κ := by
  classical
  let e : (Fin n×Bool)≃α := Fintype.equivOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hα]
    exact Nat.mul_comm n 2)
  let Q : κ→Finset (Fin n×Bool) := fun j => (T j).map e.symm.toEmbedding
  obtain ⟨U, hcard, hmoment⟩ := paired_joint_restriction Q
  refine ⟨U.map e.toEmbedding, ?_, ?_⟩
  · simpa only [Finset.card_map, Fintype.card_fin] using hcard
  · have hsub : ∀ j, Q j⊆U ↔ T j⊆U.map e.toEmbedding := by
      intro j
      rw [←Finset.map_subset_map (f:=e.toEmbedding)]
      simp [Q, Finset.map_map]
    simpa only [Q, Finset.card_map, hsub] using hmoment

variable {N n h₁ h₂ : ℕ}

theorem exists_embedded_half_support_joint (e : Fin (2*n)↪Fin N)
    (T : Fin h₁→Finset (Fin N)) :
    ∃ U : Finset (Fin N), U.card=n ∧ U⊆Finset.univ.image e ∧
      8*(∑ j, if T j⊆U then jointCost (T j).card else 0)≤105*h₁ := by
  classical
  let V : Finset (Fin N) := Finset.univ.image e
  let Q : Fin h₁→Finset (Fin (2*n)) := fun j =>
    if T j⊆V then Finset.univ.filter (fun i => e i∈T j) else ∅
  have hdecode (j : Fin h₁) (hj : T j⊆V) : (Q j).image e=T j := by
    ext i
    constructor
    · intro hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      simpa only [Q, if_pos hj, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    · intro hi
      obtain ⟨a, _, hai⟩ := Finset.mem_image.mp (hj hi)
      refine Finset.mem_image.mpr ⟨a, ?_, hai⟩
      simp only [Q, if_pos hj, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [hai]
  obtain ⟨U, hcard, hmoment⟩ := half_joint_restriction n (Fintype.card_fin (2*n)) Q
  have hUV : U.image e⊆V := Finset.image_subset_image (Finset.subset_univ U)
  have hcost :
      (∑ j, if Q j⊆U then jointCost (Q j).card else 0)=
        ∑ j, if T j⊆U.image e then jointCost (T j).card else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : T j⊆V
    · have hc : (Q j).card=(T j).card := by
        have hc := Finset.card_image_of_injective (Q j) e.injective
        rw [hdecode j hj] at hc
        exact hc.symm
      have hs : Q j⊆U ↔ T j⊆U.image e := by
        rw [←hdecode j hj]
        exact (Finset.image_subset_image_iff e.injective).symm
      simp only [hc, hs]
    · have hQ : Q j=∅ := by simp only [Q, if_neg hj]
      have hout : ¬T j⊆U.image e := fun h => hj (h.trans hUV)
      simp [hQ, hout]
  refine ⟨U.image e, ?_, hUV, ?_⟩
  · rw [Finset.card_image_of_injective U e.injective, hcard]
  · rw [←hcost]
    simpa only [Fintype.card_fin] using hmoment

theorem exists_half_support_joint (h : 2*n≤N)
    (T : Fin h₁→Finset (Fin N)) :
    ∃ U : Finset (Fin N), U.card=n ∧
      8*(∑ j, if T j⊆U then jointCost (T j).card else 0)≤105*h₁ := by
  obtain ⟨U, hcard, _, hmoment⟩ :=
    exists_embedded_half_support_joint (Fin.castLEEmb h).toEmbedding T
  exact ⟨U, hcard, hmoment⟩

theorem exists_joint_model [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x=Maximum N x) (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N), S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      16*(∑ j, (rowSupport (model.A j)).card.descFactorial 4)≤105*h₁ ∧
      8*ActualHalfRestriction.nonBraidCount model≤h₁ := by
  classical
  obtain ⟨S, hS, hbudget⟩ := exists_half_support_joint hpair
    (fun j => rowSupport (net.A j))
  subst n
  obtain ⟨model, hmax, hnorm, hrows, _⟩ :=
    exists_localized_normalized net hnet hn.1 (selectedEmbedding S)
  have hcost :
      (∑ j, jointCost (rowSupport (model.A j)).card)=
      ∑ j, if rowSupport (net.A j)⊆S then jointCost (rowSupport (net.A j)).card else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hrows j, selectedEmbedding_image]
    by_cases hs : rowSupport (net.A j)⊆S
    · rw [if_pos hs, card_rowSupport_restrict (selectedEmbedding S) (net.A j)
        (by rwa [selectedEmbedding_image]), if_pos hs]
    · simp only [if_neg hs, rowSupport_zero, Finset.card_empty, jointCost_zero]
  have hb : 8*(∑ j, jointCost (rowSupport (model.A j)).card)≤105*h₁ := by
    rw [hcost]
    exact hbudget
  have hfall : 2*(∑ j, (rowSupport (model.A j)).card.descFactorial 4)≤
      ∑ j, jointCost (rowSupport (model.A j)).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => falling_le_jointCost _
  have hcount : 105*ActualHalfRestriction.nonBraidCount model≤
      ∑ j, jointCost (rowSupport (model.A j)).card := by
    have hh := Finset.sum_le_sum (s:=Finset.univ)
      (fun j _ => count_le_jointCost (rowSupport (model.A j)).card)
    simpa only [←Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      Nat.cast_id, ActualHalfRestriction.nonBraidCount, mul_comm] using hh
  refine ⟨S, rfl, model, hmax, hnorm, ?_, ?_⟩
  · linarith only [hb, hfall]
  · linarith only [hb, hcount]

#check @exists_joint_model
#print axioms jointCost_decay
#print axioms exists_joint_model
end MaxCaterpillar.Overnight.Constants.FallingHalf
