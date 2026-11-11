import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.Weights
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.Isolated
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.Roles
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.Cardinality

/-! # A nonbraid dominant isolated gap forces the actual counted bad event

All hypotheses concern the original zero-sum real row, the full original
label-to-position permutation and its actual gap ranks. Prefix cut vanishing,
run cancellation, opposite pair weights and four distinct supported labels
are derived. No abstract run partition or bad-role witness is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
open BigOperators GoodEvent Cartesian DominantGap
variable {m : ℕ}

/-- After the full original row has been placed, its tail weights are already
in position order. The actual rank permutation is retained unchanged. -/
def positionConfig (ρ : Equiv.Perm (Fin m)) : RawConfig m := (Equiv.refl _,ρ)

lemma tail_supported (τ : Equiv.Perm (Fin (m+5))) (w : Point (m+5))
    (t : Fin m) (ht : tailWeight τ w t≠0) :
    τ.symm (tailPosition m t)∈NormalizedNetwork.rowSupport w :=
  (NormalizedNetwork.mem_rowSupport w _).mpr ht
lemma selected_supported (τ : Equiv.Perm (Fin (m+5))) (w : Point (m+5))
    (s : Fin 5) (hs : selectedWeight τ w s≠0) :
    τ.symm (selectedPosition m s)∈NormalizedNetwork.rowSupport w :=
  (NormalizedNetwork.mem_rowSupport w _).mpr hs

/-- A largest-rank nonzero gap at an isolated low-rank slot for a row of
support at least three belongs to the literal A/B/C permutation bad event. -/
theorem dominant_isolated_support_bad
    (w : Point (m+5)) (hzero : (∑ i,w i)=0)
    (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+5))) (ρ : Equiv.Perm (Fin m))
    (K : ℕ) (g : Fin m)
    (hdom : GapDominant (positionConfig ρ) (collapsedRow τ w) g)
    (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    (τ,ρ)∈supportBadConfigurations (NormalizedNetwork.rowSupport w) K := by
  classical
  let Γ := smallRankGaps ρ K
  let a := isolatedGapPredecessor g
  have hgi := (mem_isolatedGaps g Γ).mp hg
  have hsucc : a.val+1=g.val := isolatedGapPredecessor_succ g hgi.2.1
  have hab : a≠g := by
    intro he
    have hv := congrArg Fin.val he
    linarith only [hsucc,hv]
  have hc0 := collapsedRow_zeroSum τ w hzero
  have hgrank : (ρ g).val<K := (mem_smallRankGaps ρ g).mp hgi.1
  have hcuts := dominant_prefix_cuts_zero (positionConfig ρ) (collapsedRow τ w)
    hc0 K g hdom hgrank
  have hp : prefixCoeff (positionConfig ρ) (collapsedRow τ w) g.val≠0 := by
    rw [← tailCoefficient_eq_prefixCoeff (positionConfig ρ) (collapsedRow τ w) hc0 g]
    exact hdom.1
  have hv := isolated_pair_prefix_values (positionConfig ρ) (collapsedRow τ w)
    Γ hc0 hcuts g hg
  change tailWeight τ w a=prefixCoeff (positionConfig ρ) (collapsedRow τ w) g.val ∧
    tailWeight τ w g = -prefixCoeff (positionConfig ρ) (collapsedRow τ w) g.val at hv
  have ha0 : tailWeight τ w a≠0 := fun he => hp (hv.1.symm.trans he)
  have hg0 : tailWeight τ w g≠0 := by rw [hv.2]; exact neg_ne_zero.mpr hp
  have hpair : tailWeight τ w a+tailWeight τ w g=0 := by
    rw [hv.1,hv.2]
    exact add_neg_self _
  have hadj : TailAdjacent Γ a g := isolated_pair_adjacent Γ g hg
  have haS := tail_supported τ w a ha0
  have hgS := tail_supported τ w g hg0
  apply (mem_supportBadConfigurations (NormalizedNetwork.rowSupport w) K (τ,ρ)).mpr
  change τ∈supportBadAt (NormalizedNetwork.rowSupport w) Γ
  by_cases hother : ∃ z : Fin m,z≠a ∧ z≠g ∧ tailWeight τ w z≠0
  · obtain ⟨z,hza,hzg,hz⟩ := hother
    obtain hpartner | hanchor := nonzero_tail_has_run_partner (positionConfig ρ)
      (collapsedRow τ w) Γ hc0 hcuts z hz
    · obtain ⟨k,hkz,hzk,hk⟩ := hpartner
      change tailWeight τ w k≠0 at hk
      have hkout := run_partner_outside_isolated Γ g hg z k hza hzg hzk
      exact caseA_mem_supportBadAt (NormalizedNetwork.rowSupport w) Γ τ a g z k
        hab hza.symm hkout.1.symm hzg.symm hkout.2.symm hkz.symm
        haS hgS (tail_supported τ w z hz) (tail_supported τ w k hk) hadj hzk
    · obtain ⟨s,hs⟩ := selected_nonzero_of_anchor_nonzero τ w hanchor.2
      exact caseB_mem_supportBadAt (NormalizedNetwork.rowSupport w) Γ τ a g z s
        hab hza.symm hzg.symm haS hgS (tail_supported τ w z hz)
        (selected_supported τ w s hs) hadj hanchor.1
  · have honly : ∀ t : Fin m,tailWeight τ w t≠0 → t=a ∨ t=g := by
      intro t ht
      by_cases hta : t=a
      · exact Or.inl hta
      by_cases htg : t=g
      · exact Or.inr htg
      exact (hother ⟨t,hta,htg,ht⟩).elim
    obtain ⟨s,hs⟩ := selected_nonzero_of_support_three τ w a g hsupport honly
    have hsum := selected_sum_zero_of_only_opposite_pair τ w a g hab hzero hpair honly
    obtain ⟨t,_,hts,ht⟩ := exists_other_nonzero_of_sum_zero Finset.univ
      (selectedWeight τ w) hsum s (Finset.mem_univ s) hs
    exact caseC_mem_supportBadAt (NormalizedNetwork.rowSupport w) Γ τ a g s t
      hab hts.symm haS hgS (selected_supported τ w s hs) (selected_supported τ w t ht) hadj

/-- Outside the actual support bad event, a nonbraid row cannot have its
dominant nonzero gap at any retained isolated low-rank slot. -/
theorem good_event_excludes_nonbraid_dominant
    (w : Point (m+5)) (hzero : (∑ i,w i)=0)
    (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+5))) (ρ : Equiv.Perm (Fin m))
    (K : ℕ) (hgood : (τ,ρ)∉supportBadConfigurations (NormalizedNetwork.rowSupport w) K)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬GapDominant (positionConfig ρ) (collapsedRow τ w) g :=
  fun hdom => hgood (dominant_isolated_support_bad w hzero hsupport τ ρ K g hdom hg)

/-- The arbitrary actual tail order and the full-position convention have
literally the same coefficients when their original tail labels agree. -/
theorem tailCoefficient_eq_full_position_order
    (w : Point (m+5)) (τ : Equiv.Perm (Fin (m+5)))
    (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ k,v (some (p.1 k))=tailWeight τ w k) :
    tailCoefficient p v=tailCoefficient (positionConfig p.2) (collapsedRow τ w) := by
  funext g
  change -(∑ k in Finset.univ.filter (fun k : Fin m => g.val≤k.val),v (some (p.1 k)))=
    -(∑ k in Finset.univ.filter (fun k : Fin m => g.val≤k.val),tailWeight τ w k)
  congr 1
  exact Finset.sum_congr rfl (fun k _ => htail k)

/-- The same counted-event conclusion for an arbitrary original raw tail
ordering, with a literal original-label coordinate agreement. -/
theorem dominant_isolated_support_bad_of_tail_order
    (w : Point (m+5)) (hzero : (∑ i,w i)=0)
    (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+5))) (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ k,v (some (p.1 k))=tailWeight τ w k)
    (K : ℕ) (g : Fin m) (hdom : GapDominant p v g)
    (hg : g∈isolatedGaps (smallRankGaps p.2 K)) :
    (τ,p.2)∈supportBadConfigurations (NormalizedNetwork.rowSupport w) K := by
  apply dominant_isolated_support_bad w hzero hsupport τ p.2 K g ?_ hg
  change Dominant (tailCoefficient (positionConfig p.2) (collapsedRow τ w))
    (fun k => (p.2 k).val) g
  rw [← tailCoefficient_eq_full_position_order w τ p v htail]
  exact hdom

/-- The raw-order version of Good excluding every isolated dominant prefix
of an original nonbraid row, including cancellations at the selected anchor. -/
theorem good_event_excludes_nonbraid_dominant_of_tail_order
    (w : Point (m+5)) (hzero : (∑ i,w i)=0)
    (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+5))) (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ k,v (some (p.1 k))=tailWeight τ w k)
    (K : ℕ) (hgood : (τ,p.2)∉supportBadConfigurations (NormalizedNetwork.rowSupport w) K)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps p.2 K)) :
    ¬GapDominant p v g :=
  fun hdom => hgood (dominant_isolated_support_bad_of_tail_order w hzero hsupport
    τ p v htail K g hdom hg)

/-- Support three is automatically impossible at an isolated dominant slot:
the actual bad roles require four distinct supported labels. -/
theorem support_three_no_isolated_dominant
    (w : Point (m+5)) (hzero : (∑ i,w i)=0)
    (hsupport : (NormalizedNetwork.rowSupport w).card=3)
    (τ : Equiv.Perm (Fin (m+5))) (ρ : Equiv.Perm (Fin m))
    (K : ℕ) (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬GapDominant (positionConfig ρ) (collapsedRow τ w) g := by
  intro hdom
  have hbad := dominant_isolated_support_bad w hzero (by rw [hsupport]) τ ρ K g hdom hg
  have hcard := support_bad_configuration_requires_card_four
    (NormalizedNetwork.rowSupport w) K (τ,ρ) hbad
  rw [hsupport] at hcard
  norm_num at hcard

/-- The support-three consequence also holds for the original raw tail order. -/
theorem support_three_no_isolated_dominant_of_tail_order
    (w : Point (m+5)) (hzero : (∑ i,w i)=0)
    (hsupport : (NormalizedNetwork.rowSupport w).card=3)
    (τ : Equiv.Perm (Fin (m+5))) (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ k,v (some (p.1 k))=tailWeight τ w k)
    (K : ℕ) (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps p.2 K)) :
    ¬GapDominant p v g := by
  intro hdom
  have hbad := dominant_isolated_support_bad_of_tail_order w hzero
    (by rw [hsupport]) τ p v htail K g hdom hg
  have hcard := support_bad_configuration_requires_card_four
    (NormalizedNetwork.rowSupport w) K (τ,p.2) hbad
  rw [hsupport] at hcard
  norm_num at hcard

#print axioms dominant_isolated_support_bad
#print axioms good_event_excludes_nonbraid_dominant
#print axioms dominant_isolated_support_bad_of_tail_order
#print axioms good_event_excludes_nonbraid_dominant_of_tail_order
#print axioms support_three_no_isolated_dominant
#print axioms support_three_no_isolated_dominant_of_tail_order
end MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
