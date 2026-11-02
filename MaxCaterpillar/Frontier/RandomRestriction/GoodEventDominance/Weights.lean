import MaxCaterpillar.Frontier.RandomRestriction.UniformTuplesFiveTail
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.Realization
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.PrefixSwap
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Model

/-! # Actual full-row weights and the selected anchor block

The original permutation maps labels to full positions. All five selected
weights are aggregated at the anchor; no cancellation or support information
is discarded from the original row.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
open BigOperators GoodEvent Cartesian DominantGap
variable {m : ℕ}

def fullPositionEquiv (m : ℕ) : Fin 5 ⊕ Fin m ≃ Fin (m+5) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 5 m))
@[simp] theorem fullPositionEquiv_selected (s : Fin 5) :
    fullPositionEquiv m (Sum.inl s)=selectedPosition m s := by apply Fin.ext; rfl
@[simp] theorem fullPositionEquiv_tail (t : Fin m) :
    fullPositionEquiv m (Sum.inr t)=tailPosition m t := by
  apply Fin.ext
  exact Nat.add_comm 5 t.val

lemma full_position_cases (i : Fin (m+5)) :
    (∃ s : Fin 5,i=selectedPosition m s) ∨ (∃ t : Fin m,i=tailPosition m t) := by
  obtain ⟨v,hv⟩ := (fullPositionEquiv m).surjective i
  cases v with
  | inl s => exact Or.inl ⟨s,(fullPositionEquiv_selected s).symm.trans hv |>.symm⟩
  | inr t => exact Or.inr ⟨t,(fullPositionEquiv_tail t).symm.trans hv |>.symm⟩

lemma sum_full_positions (f : Fin (m+5) → ℝ) :
    (∑ i,f i)=(∑ s : Fin 5,f (selectedPosition m s))+
      ∑ t : Fin m,f (tailPosition m t) := by
  have h := Equiv.sum_comp (fullPositionEquiv m) f
  simpa only [Fintype.sum_sum_type,fullPositionEquiv_selected,fullPositionEquiv_tail] using h.symm

noncomputable def selectedWeight (τ : Equiv.Perm (Fin (m+5))) (w : Point (m+5))
    (s : Fin 5) : ℝ := w (τ.symm (selectedPosition m s))
noncomputable def tailWeight (τ : Equiv.Perm (Fin (m+5))) (w : Point (m+5))
    (t : Fin m) : ℝ := w (τ.symm (tailPosition m t))
noncomputable def collapsedRow (τ : Equiv.Perm (Fin (m+5))) (w : Point (m+5)) :
    Option (Fin m) → ℝ
  | none => ∑ s : Fin 5,selectedWeight τ w s
  | some t => tailWeight τ w t

theorem collapsedRow_sum (τ : Equiv.Perm (Fin (m+5))) (w : Point (m+5)) :
    (∑ x : Option (Fin m),collapsedRow τ w x)=∑ i,w i := by
  rw [Fintype.sum_option]
  change (∑ s : Fin 5,w (τ.symm (selectedPosition m s)))+
    (∑ t : Fin m,w (τ.symm (tailPosition m t)))=_
  calc
    _ = ∑ i,w (τ.symm i) := (sum_full_positions (fun i => w (τ.symm i))).symm
    _ = _ := Equiv.sum_comp τ.symm w

theorem collapsedRow_zeroSum (τ : Equiv.Perm (Fin (m+5))) (w : Point (m+5))
    (hw : (∑ i,w i)=0) : (∑ x : Option (Fin m),collapsedRow τ w x)=0 := by
  rw [collapsedRow_sum,hw]

/-- A nonzero summand in a zero finite sum has another nonzero summand. -/
theorem exists_other_nonzero_of_sum_zero {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α→ℝ) (hs : (∑ i in S,f i)=0)
    (a : α) (ha : a∈S) (hf : f a≠0) :
    ∃ b∈S,b≠a ∧ f b≠0 := by
  classical
  by_contra hn
  have hz : ∀ b∈S,b≠a → f b=0 := by
    intro b hb hba
    by_contra hb0
    exact hn ⟨b,hb,hba,hb0⟩
  have he : (∑ i in S,f i)=f a := Finset.sum_eq_single_of_mem a ha hz
  exact hf (he.symm.trans hs)

theorem selected_nonzero_of_anchor_nonzero (τ : Equiv.Perm (Fin (m+5)))
    (w : Point (m+5)) (ha : collapsedRow τ w none≠0) :
    ∃ s : Fin 5,selectedWeight τ w s≠0 := by
  classical
  by_contra hn
  have hs : ∀ s : Fin 5,selectedWeight τ w s=0 := by simpa only [not_exists,not_not] using hn
  exact ha (by simp only [collapsedRow,hs,Finset.sum_const_zero])

/-- With at least three supported original labels, a row whose only nonzero
tail positions are a,b must have a nonzero selected weight. -/
theorem selected_nonzero_of_support_three (τ : Equiv.Perm (Fin (m+5)))
    (w : Point (m+5)) (a b : Fin m)
    (hr : 3≤(NormalizedNetwork.rowSupport w).card)
    (honly : ∀ t : Fin m,tailWeight τ w t≠0 → t=a ∨ t=b) :
    ∃ s : Fin 5,selectedWeight τ w s≠0 := by
  classical
  by_contra hn
  have hs : ∀ s : Fin 5,selectedWeight τ w s=0 := by simpa only [not_exists,not_not] using hn
  have hsub : NormalizedNetwork.rowSupport w ⊆
      {τ.symm (tailPosition m a),τ.symm (tailPosition m b)} := by
    intro i hi
    have hwi : w i≠0 := (NormalizedNetwork.mem_rowSupport w i).mp hi
    rcases full_position_cases (τ i) with ⟨s,he⟩ | ⟨t,he⟩
    · have hi : i=τ.symm (selectedPosition m s) := by rw [← he,Equiv.symm_apply_apply]
      have hz := hs s
      change w (τ.symm (selectedPosition m s))=0 at hz
      exact (hwi (by rw [hi]; exact hz)).elim
    · have hi : i=τ.symm (tailPosition m t) := by rw [← he,Equiv.symm_apply_apply]
      have ht : tailWeight τ w t≠0 := by change w (τ.symm (tailPosition m t))≠0; rwa [← hi]
      rcases honly t ht with rfl | rfl
      · exact Finset.mem_insert.mpr (Or.inl hi)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hi))
  have hc := Finset.card_le_of_subset hsub
  have hp : ({τ.symm (tailPosition m a),τ.symm (tailPosition m b)} : Finset (Fin (m+5))).card≤2 :=
    by
      by_cases h : τ.symm (tailPosition m a)=τ.symm (tailPosition m b)
      · simp only [h,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.card_singleton]
        norm_num
      · have hn : τ.symm (tailPosition m a)∉({τ.symm (tailPosition m b)} : Finset (Fin (m+5))) := by
          simpa only [Finset.mem_singleton] using h
        rw [Finset.card_insert_of_not_mem hn,Finset.card_singleton]
  linarith only [hr,hc,hp]

/-- Cancellation of the isolated pair and absence of other tail weights
forces the entire selected block to have zero sum. -/
theorem selected_sum_zero_of_only_opposite_pair (τ : Equiv.Perm (Fin (m+5)))
    (w : Point (m+5)) (a b : Fin m) (hab : a≠b)
    (hw : (∑ i,w i)=0)
    (hpair : tailWeight τ w a+tailWeight τ w b=0)
    (honly : ∀ t : Fin m,tailWeight τ w t≠0 → t=a ∨ t=b) :
    (∑ s : Fin 5,selectedWeight τ w s)=0 := by
  classical
  have hp (t : Fin m) : tailWeight τ w t=
      (if t=a then tailWeight τ w a else 0)+(if t=b then tailWeight τ w b else 0) := by
    by_cases hta : t=a
    · subst t; simp [hab]
    · by_cases htb : t=b
      · subst t; simp [hab,Ne.symm hab]
      · have ht : tailWeight τ w t=0 := by
          by_contra hn
          exact (honly t hn).elim hta htb
        simp only [ht,if_neg hta,if_neg htb,zero_add]
  have ht : (∑ t : Fin m,tailWeight τ w t)=0 := by
    have hs : (∑ t : Fin m,tailWeight τ w t)=
        ∑ t : Fin m,((if t=a then tailWeight τ w a else 0)+
          (if t=b then tailWeight τ w b else 0)) :=
      Finset.sum_congr rfl (fun t _ => hp t)
    rw [Finset.sum_add_distrib] at hs
    have he : (∑ t : Fin m,tailWeight τ w t)=tailWeight τ w a+tailWeight τ w b := by
      simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using hs
    exact he.trans hpair
  have hc := collapsedRow_zeroSum τ w hw
  rw [Fintype.sum_option] at hc
  change (∑ s : Fin 5,selectedWeight τ w s)+(∑ t : Fin m,tailWeight τ w t)=0 at hc
  linarith only [hc,ht]

#print axioms collapsedRow_sum
#print axioms selected_nonzero_of_support_three
#print axioms selected_sum_zero_of_only_opposite_pair
end MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
