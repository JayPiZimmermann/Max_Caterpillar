import MaxCaterpillar.Frontier.RandomRestriction.FeedingCounting
import MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction

/-! Half restriction averaged only over original feeding rows. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
open BigOperators NormalizedNetwork NetworkLowerBound
variable {N n h₁ h₂ : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def feedingCard (net : NormalizedNetwork N h₁ h₂) : ℕ := by
  classical
  exact Fintype.card {j : Fin h₁ // net.Feeding j}

noncomputable def feedingEquiv (net : NormalizedNetwork N h₁ h₂) :
    Fin (feedingCard net) ≃ {j : Fin h₁ // net.Feeding j} := by
  classical
  exact (Fintype.equivFin _).symm

lemma feeding_sum (net : NormalizedNetwork N h₁ h₂) (f : Fin h₁ → ℕ) :
    (∑ i : Fin (feedingCard net),f (feedingEquiv net i).val)=
      ∑ j,if net.Feeding j then f j else 0 := by
  classical
  calc
    _ = ∑ j : {j : Fin h₁ // net.Feeding j},f j.val :=
      Fintype.sum_equiv (feedingEquiv net) _ _ (fun _ => rfl)
    _ = ∑ j in Finset.univ.filter net.Feeding,f j :=
      (Finset.sum_subtype _ (fun j => by simp only [Finset.mem_filter,Finset.mem_univ,true_and]) f).symm
    _ = _ := Finset.sum_filter _ _

theorem feedingCard_pos [NeZero N] (hN : 5≤N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x) : 1≤feedingCard net := by
  classical
  by_contra hzero
  have hc : feedingCard net=0 := Nat.eq_zero_of_not_pos (fun h => hzero h)
  have hempty : ∀ j,¬net.Feeding j := by
    intro j hj
    have hpos : 0<feedingCard net := by
      change 0<Fintype.card {j : Fin h₁ // net.Feeding j}
      exact Fintype.card_pos_iff.mpr ⟨⟨j,hj⟩⟩
    rw [hc] at hpos
    exact (Nat.lt_irrefl 0) hpos
  let e : Fin 5 ↪ Fin N := (Fin.castLEEmb hN).toEmbedding
  obtain ⟨model,hmax,hnorm,_hrows,hfeed⟩ := exists_localized_normalized net hnet hn.1 e
  have hs : ∀ j,model.Feeding j → (rowSupport (model.A j)).card≤2 := by
    intro j hj
    exact False.elim (hempty j (hfeed j hj))
  obtain ⟨k,a,b,c,d,_ha,_hb,_hc,_hd,hab,_hcd,_hac,_had,_hbc,_hbd⟩ :=
    exists_original_matching_of_feeding_braid model hnorm hs hmax
  have hW : ∀ j,model.W k j=0 := by
    intro j
    by_contra hj
    exact hempty j (hfeed j ⟨k,hj⟩)
  have hz : braidEdgeWeight model.A (model.W k) a b=0 := by
    simp only [braidEdgeWeight,hW,zero_mul,Finset.sum_const_zero,neg_zero]
  exact hab.2 hz

theorem exists_feeding_half_model [NeZero N] [NeZero n]
    (hN : 5≤N) (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (hnet : ∀ x,net.eval x=Maximum N x)
    (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N),S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x,model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      4*ActualHalfRestriction.fourthMoment (core model)≤81*feedingCard net ∧
      4*ActualHalfRestriction.nonBraidCount (core model)≤feedingCard net ∧
      4*regularizedMoment (core model)≤81*feedingCard net := by
  classical
  let T : Fin (feedingCard net) → Finset (Fin N) :=
    fun i => rowSupport (net.A (feedingEquiv net i).val)
  obtain ⟨S,hS,hbudget⟩ := ActualHalfRestriction.exists_half_support_fourth_moment hpair T
  subst n
  obtain ⟨model,hmax,hnorm,hrows,hfeed⟩ :=
    exists_localized_normalized net hnet hn.1 (selectedEmbedding S)
  have hcost : ActualHalfRestriction.fourthMoment (core model)≤
      ∑ j,if net.Feeding j then
        (if 3≤(rowSupport (net.A j)).card ∧ rowSupport (net.A j)⊆S
          then (rowSupport (net.A j)).card^4 else 0) else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : model.Feeding j
    · have hf := hfeed j hj
      simp only [core,if_pos hj,if_pos hf]
      rw [hrows j,selectedEmbedding_image]
      by_cases hs : rowSupport (net.A j)⊆S
      · rw [if_pos hs,card_rowSupport_restrict (selectedEmbedding S) (net.A j)
          (by rwa [selectedEmbedding_image])]
        simp only [hs,and_true,le_refl]
      · simp only [if_neg hs,rowSupport_zero,Finset.card_empty,show ¬3≤0 from by decide,
          and_false,ite_false,le_refl,Nat.zero_le]
    · simp only [core,if_neg hj,rowSupport_zero,Finset.card_empty,
        show ¬3≤0 from by decide,ite_false,Nat.zero_le]
  have hraw : 4*ActualHalfRestriction.fourthMoment (core model)≤81*feedingCard net := by
    have he := feeding_sum net (fun j => if 3≤(rowSupport (net.A j)).card ∧ rowSupport (net.A j)⊆S
      then (rowSupport (net.A j)).card^4 else 0)
    change 4*(∑ i : Fin (feedingCard net),
      if 3≤(rowSupport (net.A (feedingEquiv net i).val)).card ∧
        rowSupport (net.A (feedingEquiv net i).val)⊆S
      then (rowSupport (net.A (feedingEquiv net i).val)).card^4 else 0)≤81*feedingCard net at hbudget
    rw [he] at hbudget
    exact (Nat.mul_le_mul_left 4 hcost).trans hbudget
  have hcount : 4*ActualHalfRestriction.nonBraidCount (core model)≤feedingCard net := by
    have hh := ActualHalfRestriction.moment_controls_count (core model)
    linarith only [hh,hraw]
  have hreg : 4*regularizedMoment (core model)≤81*feedingCard net := by
    have hp := feedingCard_pos hN net hn hnet
    rcases le_total (ActualHalfRestriction.fourthMoment (core model)) 1 with h|h
    · rw [regularizedMoment,max_eq_right h]
      linarith only [hp]
    · rw [regularizedMoment,max_eq_left h]
      exact hraw
  exact ⟨S,rfl,model,hmax,hnorm,hraw,hcount,hreg⟩

#print axioms feedingCard_pos
#print axioms exists_feeding_half_model
end MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
