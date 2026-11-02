import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.SamplingGeometry
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.Weights

/-! # Original support and anchor aggregation for an actual selected subset

No full-position permutation or reindexing of the original ambient labels is
introduced. The tail embedding is the existing Sampling enumeration.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
open BigOperators Sampling
variable {n : ℕ}

noncomputable def tailWeight (S : Finset (Fin n))
    (τ : Equiv.Perm (Fin (tailCount S))) (w : Point n) (t : Fin (tailCount S)) : ℝ :=
  w (tail S (τ t))

/-- A nonzero collapsed anchor supplies an actual nonzero selected label. -/
theorem selected_nonzero_of_anchor_nonzero (S : Finset (Fin n)) (w : Point n)
    (ha : DominantGap.collapsedRow (tail S) w none≠0) :
    ∃ s∈S,w s≠0 := by
  classical
  rw [Sampling.collapsedRow_none] at ha
  by_contra hn
  apply ha
  apply Finset.sum_eq_zero
  intro s hs
  by_contra hw
  exact hn ⟨s,hs,hw⟩

/-- Original support of size at least three cannot fit in two tail labels
when every actual selected weight vanishes. -/
theorem selected_nonzero_of_support_three (S : Finset (Fin n))
    (τ : Equiv.Perm (Fin (tailCount S))) (w : Point n)
    (a b : Fin (tailCount S)) (hr : 3≤(NormalizedNetwork.rowSupport w).card)
    (honly : ∀ t,tailWeight S τ w t≠0 → t=a ∨ t=b) :
    ∃ s∈S,w s≠0 := by
  classical
  by_contra hn
  have hs : ∀ s∈S,w s=0 := by
    intro s hs
    by_contra hw
    exact hn ⟨s,hs,hw⟩
  have hsub : NormalizedNetwork.rowSupport w ⊆ {tail S (τ a),tail S (τ b)} := by
    intro i hi
    have hwi := (NormalizedNetwork.mem_rowSupport w i).mp hi
    by_cases hiS : i∈S
    · exact (hwi (hs i hiS)).elim
    obtain ⟨t,ht⟩ := (tail_range S i).mpr hiS
    have hw : tailWeight S τ w (τ.symm t)≠0 := by
      change w (tail S (τ (τ.symm t)))≠0
      rwa [Equiv.apply_symm_apply,ht]
    rcases honly (τ.symm t) hw with ha | hb
    · apply Finset.mem_insert.mpr
      left
      rw [←ha,Equiv.apply_symm_apply,ht]
    · apply Finset.mem_insert.mpr
      right
      apply Finset.mem_singleton.mpr
      rw [←hb,Equiv.apply_symm_apply,ht]
  have hc := Finset.card_le_of_subset hsub
  have hp : ({tail S (τ a),tail S (τ b)} : Finset (Fin n)).card≤2 := by
    by_cases h : tail S (τ a)=tail S (τ b)
    · simp only [h,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.card_singleton]
      norm_num
    · have hn : tail S (τ a)∉({tail S (τ b)} : Finset (Fin n)) := by
        simpa only [Finset.mem_singleton] using h
      rw [Finset.card_insert_of_not_mem hn,Finset.card_singleton]
  linarith only [hr,hc,hp]

/-- If the only nonzero tail weights are one opposite pair, the actual
selected block has zero total weight, even when its individual entries cancel. -/
theorem selected_sum_zero_of_only_opposite_pair (S : Finset (Fin n))
    (τ : Equiv.Perm (Fin (tailCount S))) (w : Point n)
    (a b : Fin (tailCount S)) (hab : a≠b) (hw : (∑ i,w i)=0)
    (hpair : tailWeight S τ w a+tailWeight S τ w b=0)
    (honly : ∀ t,tailWeight S τ w t≠0 → t=a ∨ t=b) :
    (∑ s in S,w s)=0 := by
  classical
  have hp (t : Fin (tailCount S)) : tailWeight S τ w t=
      (if t=a then tailWeight S τ w a else 0)+(if t=b then tailWeight S τ w b else 0) := by
    by_cases hta : t=a
    · subst t
      simp [hab]
    · by_cases htb : t=b
      · subst t
        simp [hab,Ne.symm hab]
      · have ht : tailWeight S τ w t=0 := by
          by_contra hn
          exact (honly t hn).elim hta htb
        simp only [ht,if_neg hta,if_neg htb,zero_add]
  have ht : (∑ t : Fin (tailCount S),tailWeight S τ w t)=0 := by
    have hs : (∑ t : Fin (tailCount S),tailWeight S τ w t)=
        ∑ t : Fin (tailCount S),((if t=a then tailWeight S τ w a else 0)+
          (if t=b then tailWeight S τ w b else 0)) := Finset.sum_congr rfl (fun t _ => hp t)
    rw [Finset.sum_add_distrib] at hs
    have he : (∑ t : Fin (tailCount S),tailWeight S τ w t)=tailWeight S τ w a+tailWeight S τ w b := by
      simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using hs
    exact he.trans hpair
  have hper := Equiv.sum_comp τ (fun t => w (tail S t))
  change (∑ t : Fin (tailCount S),tailWeight S τ w t)=(∑ t : Fin (tailCount S),w (tail S t)) at hper
  have htail : (∑ t : Fin (tailCount S),w (tail S t))=0 := hper.symm.trans ht
  have hc := DominantGap.collapsedRow_zero_sum (tail S) w hw
  rw [Fintype.sum_option,Sampling.collapsedRow_none] at hc
  change (∑ s in S,w s)+(∑ t : Fin (tailCount S),w (tail S t))=0 at hc
  linarith only [hc,htail]

#print axioms selected_nonzero_of_anchor_nonzero
#print axioms selected_nonzero_of_support_three
#print axioms selected_sum_zero_of_only_opposite_pair
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
