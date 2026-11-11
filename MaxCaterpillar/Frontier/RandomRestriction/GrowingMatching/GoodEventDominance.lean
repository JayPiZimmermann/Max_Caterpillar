import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.Weights
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.Roles
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.Cardinality
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.Isolated

/-! # Actual dominant-gap bad-event semantics for every selected arity

The original support is retained when all k selected entries are aggregated
at the anchor. Every run/cancellation/role witness is derived, uniformly in k,
including k=0 and k=1. The old selected-five production sources are unchanged.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance
open BigOperators Configurations Cartesian DominantGap GoodEvent
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
  (isolatedGaps smallRankGaps mem_isolatedGaps mem_smallRankGaps
   isolatedGapPredecessor isolatedGapPredecessor_succ TailAdjacent TailSameRun AnchorSameRun)
open MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
  (dominant_prefix_cuts_zero isolated_pair_prefix_values isolated_pair_adjacent
   run_partner_outside_isolated nonzero_tail_has_run_partner exists_other_nonzero_of_sum_zero)
variable {m : ℕ}

/-- After the full original row has been placed, its tail weights are already
in position order. The actual rank permutation is retained unchanged. -/
def positionConfig (ρ : Equiv.Perm (Fin m)) : RawConfig m := (Equiv.refl _,ρ)

lemma tail_supported (k : ℕ) (τ : Equiv.Perm (Fin (m+k))) (w : Point (m+k))
    (t : Fin m) (ht : tailWeight k τ w t≠0) :
    τ.symm (tailPosition k m t)∈NormalizedNetwork.rowSupport w :=
  (NormalizedNetwork.mem_rowSupport w _).mpr ht
lemma selected_supported (k : ℕ) (τ : Equiv.Perm (Fin (m+k))) (w : Point (m+k))
    (s : Fin k) (hs : selectedWeight k τ w s≠0) :
    τ.symm (selectedPosition k m s)∈NormalizedNetwork.rowSupport w :=
  (NormalizedNetwork.mem_rowSupport w _).mpr hs

/-- A largest-rank nonzero gap at an isolated low-rank slot for a row of
support at least three belongs to the literal A/B/C permutation bad event. -/
theorem dominant_isolated_support_bad (k : ℕ)
    (w : Point (m+k)) (hzero : (∑ i,w i)=0)
    (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+k))) (ρ : Equiv.Perm (Fin m))
    (K : ℕ) (g : Fin m)
    (hdom : GapDominant (positionConfig ρ) (collapsedRow k τ w) g)
    (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    (τ,ρ)∈supportBadConfigurations k (NormalizedNetwork.rowSupport w) K := by
  classical
  let Γ := smallRankGaps ρ K
  let a := isolatedGapPredecessor g
  have hgi := (mem_isolatedGaps g Γ).mp hg
  have hsucc : a.val+1=g.val := isolatedGapPredecessor_succ g hgi.2.1
  have hab : a≠g := by
    intro he
    have hv := congrArg Fin.val he
    linarith only [hsucc,hv]
  have hc0 := collapsedRow_zeroSum k τ w hzero
  have hgrank : (ρ g).val<K := (mem_smallRankGaps ρ g).mp hgi.1
  have hcuts := dominant_prefix_cuts_zero (positionConfig ρ) (collapsedRow k τ w)
    hc0 K g hdom hgrank
  have hp : prefixCoeff (positionConfig ρ) (collapsedRow k τ w) g.val≠0 := by
    rw [← tailCoefficient_eq_prefixCoeff (positionConfig ρ) (collapsedRow k τ w) hc0 g]
    exact hdom.1
  have hv := isolated_pair_prefix_values (positionConfig ρ) (collapsedRow k τ w)
    Γ hc0 hcuts g hg
  change tailWeight k τ w a=prefixCoeff (positionConfig ρ) (collapsedRow k τ w) g.val ∧
    tailWeight k τ w g = -prefixCoeff (positionConfig ρ) (collapsedRow k τ w) g.val at hv
  have ha0 : tailWeight k τ w a≠0 := fun he => hp (hv.1.symm.trans he)
  have hg0 : tailWeight k τ w g≠0 := by rw [hv.2]; exact neg_ne_zero.mpr hp
  have hpair : tailWeight k τ w a+tailWeight k τ w g=0 := by
    rw [hv.1,hv.2]
    exact add_neg_self _
  have hadj : TailAdjacent Γ a g := isolated_pair_adjacent Γ g hg
  have haS := tail_supported k τ w a ha0
  have hgS := tail_supported k τ w g hg0
  apply (mem_supportBadConfigurations k (NormalizedNetwork.rowSupport w) K (τ,ρ)).mpr
  change τ∈supportBadAt k (NormalizedNetwork.rowSupport w) Γ
  by_cases hother : ∃ z : Fin m,z≠a ∧ z≠g ∧ tailWeight k τ w z≠0
  · obtain ⟨z,hza,hzg,hz⟩ := hother
    obtain hpartner | hanchor := nonzero_tail_has_run_partner (positionConfig ρ)
      (collapsedRow k τ w) Γ hc0 hcuts z hz
    · obtain ⟨j,hkz,hzk,hk⟩ := hpartner
      change tailWeight k τ w j≠0 at hk
      have hkout := run_partner_outside_isolated Γ g hg z j hza hzg hzk
      exact caseA_mem_supportBadAt (k:=k) (NormalizedNetwork.rowSupport w) Γ τ a g z j
        hab hza.symm hkout.1.symm hzg.symm hkout.2.symm hkz.symm
        haS hgS (tail_supported k τ w z hz) (tail_supported k τ w j hk) hadj hzk
    · obtain ⟨s,hs⟩ := selected_nonzero_of_anchor_nonzero k τ w hanchor.2
      exact caseB_mem_supportBadAt (k:=k) (NormalizedNetwork.rowSupport w) Γ τ a g z s
        hab hza.symm hzg.symm haS hgS (tail_supported k τ w z hz)
        (selected_supported k τ w s hs) hadj hanchor.1
  · have honly : ∀ t : Fin m,tailWeight k τ w t≠0 → t=a ∨ t=g := by
      intro t ht
      by_cases hta : t=a
      · exact Or.inl hta
      by_cases htg : t=g
      · exact Or.inr htg
      exact (hother ⟨t,hta,htg,ht⟩).elim
    obtain ⟨s,hs⟩ := selected_nonzero_of_support_three k τ w a g hsupport honly
    have hsum := selected_sum_zero_of_only_opposite_pair k τ w a g hab hzero hpair honly
    obtain ⟨t,_,hts,ht⟩ := exists_other_nonzero_of_sum_zero Finset.univ
      (selectedWeight k τ w) hsum s (Finset.mem_univ s) hs
    exact caseC_mem_supportBadAt (k:=k) (NormalizedNetwork.rowSupport w) Γ τ a g s t
      hab hts.symm haS hgS (selected_supported k τ w s hs) (selected_supported k τ w t ht) hadj

/-- Outside the actual support bad event, a nonbraid row cannot have its
dominant nonzero gap at any retained isolated low-rank slot. -/
theorem good_event_excludes_nonbraid_dominant (k : ℕ)
    (w : Point (m+k)) (hzero : (∑ i,w i)=0)
    (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+k))) (ρ : Equiv.Perm (Fin m))
    (K : ℕ) (hgood : (τ,ρ)∉supportBadConfigurations k (NormalizedNetwork.rowSupport w) K)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬GapDominant (positionConfig ρ) (collapsedRow k τ w) g :=
  fun hdom => hgood (dominant_isolated_support_bad k w hzero hsupport τ ρ K g hdom hg)

/-- The arbitrary actual tail order and the full-position convention have
literally the same coefficients when their original tail labels agree. -/
theorem tailCoefficient_eq_full_position_order (k : ℕ)
    (w : Point (m+k)) (τ : Equiv.Perm (Fin (m+k)))
    (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ j,v (some (p.1 j))=tailWeight k τ w j) :
    tailCoefficient p v=tailCoefficient (positionConfig p.2) (collapsedRow k τ w) := by
  funext g
  change -(∑ j in Finset.univ.filter (fun j : Fin m => g.val≤j.val),v (some (p.1 j)))=
    -(∑ j in Finset.univ.filter (fun j : Fin m => g.val≤j.val),tailWeight k τ w j)
  congr 1
  exact Finset.sum_congr rfl (fun j _ => htail j)

/-- The same counted-event conclusion for an arbitrary original raw tail
ordering, with a literal original-label coordinate agreement. -/
theorem dominant_isolated_support_bad_of_tail_order (k : ℕ)
    (w : Point (m+k)) (hzero : (∑ i,w i)=0)
    (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+k))) (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ j,v (some (p.1 j))=tailWeight k τ w j)
    (K : ℕ) (g : Fin m) (hdom : GapDominant p v g)
    (hg : g∈isolatedGaps (smallRankGaps p.2 K)) :
    (τ,p.2)∈supportBadConfigurations k (NormalizedNetwork.rowSupport w) K := by
  apply dominant_isolated_support_bad k w hzero hsupport τ p.2 K g ?_ hg
  change Dominant (tailCoefficient (positionConfig p.2) (collapsedRow k τ w))
    (fun j => (p.2 j).val) g
  rw [← tailCoefficient_eq_full_position_order k w τ p v htail]
  exact hdom

/-- The raw-order version of Good excluding every isolated dominant prefix
of an original nonbraid row, including cancellations at the selected anchor. -/
theorem good_event_excludes_nonbraid_dominant_of_tail_order (k : ℕ)
    (w : Point (m+k)) (hzero : (∑ i,w i)=0)
    (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+k))) (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ j,v (some (p.1 j))=tailWeight k τ w j)
    (K : ℕ) (hgood : (τ,p.2)∉supportBadConfigurations k (NormalizedNetwork.rowSupport w) K)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps p.2 K)) :
    ¬GapDominant p v g :=
  fun hdom => hgood (dominant_isolated_support_bad_of_tail_order k w hzero hsupport
    τ p v htail K g hdom hg)

/-- Support three is automatically impossible at an isolated dominant slot:
the actual bad roles require four distinct supported labels. -/
theorem support_three_no_isolated_dominant (k : ℕ)
    (w : Point (m+k)) (hzero : (∑ i,w i)=0)
    (hsupport : (NormalizedNetwork.rowSupport w).card=3)
    (τ : Equiv.Perm (Fin (m+k))) (ρ : Equiv.Perm (Fin m))
    (K : ℕ) (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬GapDominant (positionConfig ρ) (collapsedRow k τ w) g := by
  intro hdom
  have hbad := dominant_isolated_support_bad k w hzero (by rw [hsupport]) τ ρ K g hdom hg
  have hcard := support_bad_configuration_requires_card_four k
    (NormalizedNetwork.rowSupport w) K (τ,ρ) hbad
  rw [hsupport] at hcard
  norm_num at hcard

/-- The support-three consequence also holds for the original raw tail order. -/
theorem support_three_no_isolated_dominant_of_tail_order (k : ℕ)
    (w : Point (m+k)) (hzero : (∑ i,w i)=0)
    (hsupport : (NormalizedNetwork.rowSupport w).card=3)
    (τ : Equiv.Perm (Fin (m+k))) (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ j,v (some (p.1 j))=tailWeight k τ w j)
    (K : ℕ) (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps p.2 K)) :
    ¬GapDominant p v g := by
  intro hdom
  have hbad := dominant_isolated_support_bad_of_tail_order k w hzero
    (by rw [hsupport]) τ p v htail K g hdom hg
  have hcard := support_bad_configuration_requires_card_four k
    (NormalizedNetwork.rowSupport w) K (τ,p.2) hbad
  rw [hsupport] at hcard
  norm_num at hcard

#print axioms dominant_isolated_support_bad
#print axioms good_event_excludes_nonbraid_dominant
#print axioms dominant_isolated_support_bad_of_tail_order
#print axioms good_event_excludes_nonbraid_dominant_of_tail_order
#print axioms support_three_no_isolated_dominant
#print axioms support_three_no_isolated_dominant_of_tail_order
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance
