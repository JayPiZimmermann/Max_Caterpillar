import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConfigurationsSums
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.Weights

/-! # Original real rows and selected-anchor aggregation at arbitrary arity

Every selected coordinate is retained in the original support. The collapse
only sums the selected weights for evaluating prefixes, and preserves the
complete row sum. All results include k=0 and k=1 without added premises.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance
open BigOperators Configurations
variable {m : ℕ}

noncomputable def selectedWeight (k : ℕ) (τ : Equiv.Perm (Fin (m+k))) (w : Point (m+k))
    (s : Fin k) : ℝ := w (τ.symm (selectedPosition k m s))
noncomputable def tailWeight (k : ℕ) (τ : Equiv.Perm (Fin (m+k))) (w : Point (m+k))
    (t : Fin m) : ℝ := w (τ.symm (tailPosition k m t))
noncomputable def collapsedRow (k : ℕ) (τ : Equiv.Perm (Fin (m+k))) (w : Point (m+k)) :
    Option (Fin m) → ℝ
  | none => ∑ s : Fin k,selectedWeight k τ w s
  | some t => tailWeight k τ w t

theorem collapsedRow_sum (k : ℕ) (τ : Equiv.Perm (Fin (m+k))) (w : Point (m+k)) :
    (∑ x : Option (Fin m),collapsedRow k τ w x)=∑ i,w i := by
  rw [Fintype.sum_option]
  change (∑ s : Fin k,w (τ.symm (selectedPosition k m s)))+
    (∑ t : Fin m,w (τ.symm (tailPosition k m t)))=_
  calc
    _ = ∑ i,w (τ.symm i) := (sum_full_positions (fun i => w (τ.symm i))).symm
    _ = _ := Equiv.sum_comp τ.symm w

theorem collapsedRow_zeroSum (k : ℕ) (τ : Equiv.Perm (Fin (m+k))) (w : Point (m+k))
    (hw : (∑ i,w i)=0) : (∑ x : Option (Fin m),collapsedRow k τ w x)=0 := by
  rw [collapsedRow_sum,hw]

theorem selected_nonzero_of_anchor_nonzero (k : ℕ) (τ : Equiv.Perm (Fin (m+k)))
    (w : Point (m+k)) (ha : collapsedRow k τ w none≠0) :
    ∃ s : Fin k,selectedWeight k τ w s≠0 := by
  classical
  by_contra hn
  have hs : ∀ s : Fin k,selectedWeight k τ w s=0 := by simpa only [not_exists,not_not] using hn
  exact ha (by simp only [collapsedRow,hs,Finset.sum_const_zero])

/-- With at least three supported original labels, a row whose only nonzero
tail positions are a,b must have a nonzero selected weight. -/
theorem selected_nonzero_of_support_three (k : ℕ) (τ : Equiv.Perm (Fin (m+k)))
    (w : Point (m+k)) (a b : Fin m)
    (hr : 3≤(NormalizedNetwork.rowSupport w).card)
    (honly : ∀ t : Fin m,tailWeight k τ w t≠0 → t=a ∨ t=b) :
    ∃ s : Fin k,selectedWeight k τ w s≠0 := by
  classical
  by_contra hn
  have hs : ∀ s : Fin k,selectedWeight k τ w s=0 := by simpa only [not_exists,not_not] using hn
  have hsub : NormalizedNetwork.rowSupport w ⊆
      {τ.symm (tailPosition k m a),τ.symm (tailPosition k m b)} := by
    intro i hi
    have hwi : w i≠0 := (NormalizedNetwork.mem_rowSupport w i).mp hi
    rcases full_position_cases (k:=k) (m:=m) (τ i) with ⟨s,he⟩ | ⟨t,he⟩
    · have hi : i=τ.symm (selectedPosition k m s) := by rw [← he,Equiv.symm_apply_apply]
      have hz := hs s
      change w (τ.symm (selectedPosition k m s))=0 at hz
      exact (hwi (by rw [hi]; exact hz)).elim
    · have hi : i=τ.symm (tailPosition k m t) := by rw [← he,Equiv.symm_apply_apply]
      have ht : tailWeight k τ w t≠0 := by change w (τ.symm (tailPosition k m t))≠0; rwa [← hi]
      rcases honly t ht with rfl | rfl
      · exact Finset.mem_insert.mpr (Or.inl hi)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hi))
  have hc := Finset.card_le_of_subset hsub
  have hp : ({τ.symm (tailPosition k m a),τ.symm (tailPosition k m b)} : Finset (Fin (m+k))).card≤2 :=
    by
      by_cases h : τ.symm (tailPosition k m a)=τ.symm (tailPosition k m b)
      · simp only [h,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.card_singleton]
        norm_num
      · have hn : τ.symm (tailPosition k m a)∉({τ.symm (tailPosition k m b)} : Finset (Fin (m+k))) := by
          simpa only [Finset.mem_singleton] using h
        rw [Finset.card_insert_of_not_mem hn,Finset.card_singleton]
  linarith only [hr,hc,hp]

/-- Cancellation of the isolated pair and absence of other tail weights
forces the entire selected block to have zero sum. -/
theorem selected_sum_zero_of_only_opposite_pair (k : ℕ) (τ : Equiv.Perm (Fin (m+k)))
    (w : Point (m+k)) (a b : Fin m) (hab : a≠b)
    (hw : (∑ i,w i)=0)
    (hpair : tailWeight k τ w a+tailWeight k τ w b=0)
    (honly : ∀ t : Fin m,tailWeight k τ w t≠0 → t=a ∨ t=b) :
    (∑ s : Fin k,selectedWeight k τ w s)=0 := by
  classical
  have hp (t : Fin m) : tailWeight k τ w t=
      (if t=a then tailWeight k τ w a else 0)+(if t=b then tailWeight k τ w b else 0) := by
    by_cases hta : t=a
    · subst t; simp [hab]
    · by_cases htb : t=b
      · subst t; simp [hab,Ne.symm hab]
      · have ht : tailWeight k τ w t=0 := by
          by_contra hn
          exact (honly t hn).elim hta htb
        simp only [ht,if_neg hta,if_neg htb,zero_add]
  have ht : (∑ t : Fin m,tailWeight k τ w t)=0 := by
    have hs : (∑ t : Fin m,tailWeight k τ w t)=
        ∑ t : Fin m,((if t=a then tailWeight k τ w a else 0)+
          (if t=b then tailWeight k τ w b else 0)) :=
      Finset.sum_congr rfl (fun t _ => hp t)
    rw [Finset.sum_add_distrib] at hs
    have he : (∑ t : Fin m,tailWeight k τ w t)=tailWeight k τ w a+tailWeight k τ w b := by
      simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using hs
    exact he.trans hpair
  have hc := collapsedRow_zeroSum k τ w hw
  rw [Fintype.sum_option] at hc
  change (∑ s : Fin k,selectedWeight k τ w s)+(∑ t : Fin m,tailWeight k τ w t)=0 at hc
  linarith only [hc,ht]

#print axioms collapsedRow_sum
#print axioms selected_nonzero_of_support_three
#print axioms selected_sum_zero_of_only_opposite_pair
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance
