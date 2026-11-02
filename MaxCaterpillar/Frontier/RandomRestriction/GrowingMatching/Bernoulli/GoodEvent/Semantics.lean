import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Weights
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Events
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.Isolated
import MaxCaterpillar.Frontier.RandomRestriction.ActualClean

/-! # Intrinsic selected-subset good events imply actual cleanliness

All supports remain subsets of the original Fin n labels. The original tail
order acts through Sampling.tail, and the frozen dominant-gap collapsed row
collects the complete selected sum. Prefix cuts, run partners and actual bad
roles are conclusions, not hypotheses of the headline.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
open BigOperators Sampling Cartesian DominantGap
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
  (isolatedGaps smallRankGaps mem_isolatedGaps mem_smallRankGaps
   isolatedGapPredecessor isolatedGapPredecessor_succ TailAdjacent TailSameRun AnchorSameRun)
open MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
  (dominant_prefix_cuts_zero isolated_pair_prefix_values isolated_pair_adjacent
   run_partner_outside_isolated nonzero_tail_has_run_partner exists_other_nonzero_of_sum_zero)
variable {n : ℕ}

lemma tail_supported (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S)))
    (w : Point n) (t : Fin (tailCount S)) (ht : tailWeight S τ w t≠0) :
    tail S (τ t)∈NormalizedNetwork.rowSupport w :=
  (NormalizedNetwork.mem_rowSupport w _).mpr ht

/-- An actual zero-sum original nonbraid row with an isolated dominant gap
forces membership in the literal original-label A/B/C bad event. -/
theorem dominant_isolated_support_bad (S : Finset (Fin n)) (w : Point n)
    (hzero : (∑ i,w i)=0) (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ ρ : Equiv.Perm (Fin (tailCount S))) (K : ℕ) (g : Fin (tailCount S))
    (hdom : GapDominant (τ,ρ) (DominantGap.collapsedRow (tail S) w) g)
    (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    (τ,ρ)∈supportBadConfigurations (NormalizedNetwork.rowSupport w) S K := by
  classical
  let Γ := smallRankGaps ρ K
  let a := isolatedGapPredecessor g
  have hgi := (mem_isolatedGaps g Γ).mp hg
  have hsucc : a.val+1=g.val := isolatedGapPredecessor_succ g hgi.2.1
  have hab : a≠g := by
    intro he
    have hv := congrArg Fin.val he
    linarith only [hsucc,hv]
  have hc0 := DominantGap.collapsedRow_zero_sum (tail S) w hzero
  have hgrank : (ρ g).val<K := (mem_smallRankGaps ρ g).mp hgi.1
  have hcuts := dominant_prefix_cuts_zero (τ,ρ) (DominantGap.collapsedRow (tail S) w)
    hc0 K g hdom hgrank
  have hp : prefixCoeff (τ,ρ) (DominantGap.collapsedRow (tail S) w) g.val≠0 := by
    rw [← tailCoefficient_eq_prefixCoeff (τ,ρ) (DominantGap.collapsedRow (tail S) w) hc0 g]
    exact hdom.1
  have hv := isolated_pair_prefix_values (τ,ρ) (DominantGap.collapsedRow (tail S) w)
    Γ hc0 hcuts g hg
  change tailWeight S τ w a=prefixCoeff (τ,ρ) (DominantGap.collapsedRow (tail S) w) g.val ∧
    tailWeight S τ w g = -prefixCoeff (τ,ρ) (DominantGap.collapsedRow (tail S) w) g.val at hv
  have ha0 : tailWeight S τ w a≠0 := fun he => hp (hv.1.symm.trans he)
  have hg0 : tailWeight S τ w g≠0 := by rw [hv.2]; exact neg_ne_zero.mpr hp
  have hpair : tailWeight S τ w a+tailWeight S τ w g=0 := by
    rw [hv.1,hv.2]
    exact add_neg_self _
  have hadj : TailAdjacent Γ a g := isolated_pair_adjacent Γ g hg
  have haT := tail_supported S τ w a ha0
  have hgT := tail_supported S τ w g hg0
  apply (mem_supportBadConfigurations (NormalizedNetwork.rowSupport w) S K (τ,ρ)).mpr
  change τ∈supportBadAt (NormalizedNetwork.rowSupport w) S Γ
  by_cases hother : ∃ z : Fin (tailCount S),z≠a ∧ z≠g ∧ tailWeight S τ w z≠0
  · obtain ⟨z,hza,hzg,hz⟩ := hother
    obtain hpartner | hanchor := nonzero_tail_has_run_partner (τ,ρ)
      (DominantGap.collapsedRow (tail S) w) Γ hc0 hcuts z hz
    · obtain ⟨j,hjz,hzj,hj⟩ := hpartner
      change tailWeight S τ w j≠0 at hj
      have hjout := run_partner_outside_isolated Γ g hg z j hza hzg hzj
      exact caseA_mem_supportBadAt (NormalizedNetwork.rowSupport w) S Γ τ a g z j
        hab hza.symm hjout.1.symm hzg.symm hjout.2.symm hjz.symm
        haT hgT (tail_supported S τ w z hz) (tail_supported S τ w j hj) hadj hzj
    · obtain ⟨s,hsS,hs⟩ := selected_nonzero_of_anchor_nonzero S w hanchor.2
      have hsT := (NormalizedNetwork.mem_rowSupport w s).mpr hs
      exact caseB_mem_supportBadAt (NormalizedNetwork.rowSupport w) S Γ τ a g z s
        hab hza.symm hzg.symm haT hgT (tail_supported S τ w z hz) hsT hsS hadj hanchor.1
  · have honly : ∀ t : Fin (tailCount S),tailWeight S τ w t≠0 → t=a ∨ t=g := by
      intro t ht
      by_cases hta : t=a
      · exact Or.inl hta
      by_cases htg : t=g
      · exact Or.inr htg
      exact (hother ⟨t,hta,htg,ht⟩).elim
    obtain ⟨s,hsS,hs⟩ := selected_nonzero_of_support_three S τ w a g hsupport honly
    have hsum := selected_sum_zero_of_only_opposite_pair S τ w a g hab hzero hpair honly
    obtain ⟨t,htS,hts,ht⟩ := exists_other_nonzero_of_sum_zero S w hsum s hsS hs
    have hsT := (NormalizedNetwork.mem_rowSupport w s).mpr hs
    have htT := (NormalizedNetwork.mem_rowSupport w t).mpr ht
    exact caseC_mem_supportBadAt (NormalizedNetwork.rowSupport w) S Γ τ a g s t
      hab hts.symm haT hgT hsT htT hsS htS hadj

/-- Original-support Good forbids all isolated dominant gaps of a nonbraid row. -/
theorem good_event_excludes_nonbraid_dominant (S : Finset (Fin n)) (w : Point n)
    (hzero : (∑ i,w i)=0) (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ ρ : Equiv.Perm (Fin (tailCount S))) (K : ℕ)
    (hgood : (τ,ρ)∉supportBadConfigurations (NormalizedNetwork.rowSupport w) S K)
    (g : Fin (tailCount S)) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬GapDominant (τ,ρ) (DominantGap.collapsedRow (tail S) w) g :=
  fun hd => hgood (dominant_isolated_support_bad S w hzero hsupport τ ρ K g hd hg)

/-- The union over an arbitrary finite family still concerns the original
row supports, before any selected-anchor cancellation. -/
theorem family_good_excludes_dominant {κ : Type*} [Fintype κ]
    (rows : κ→Point n) (hzero : ∀ j,(∑ i,rows j i)=0) (S : Finset (Fin n))
    (τ ρ : Equiv.Perm (Fin (tailCount S))) (K : ℕ)
    (hgood : (τ,ρ)∉familyBadConfigurations (fun j => NormalizedNetwork.rowSupport (rows j)) S K)
    (j : κ) (hsupport : 3≤(NormalizedNetwork.rowSupport (rows j)).card)
    (g : Fin (tailCount S)) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬GapDominant (τ,ρ) (DominantGap.collapsedRow (tail S) (rows j)) g := by
  intro hd
  apply hgood
  apply (mem_familyBadConfigurations _ S K (τ,ρ)).mpr
  exact ⟨j,dominant_isolated_support_bad S (rows j) (hzero j) hsupport τ ρ K g hd hg⟩

noncomputable def firstSupports {h₁ h₂ : ℕ} (net : NormalizedNetwork n h₁ h₂) :
    Fin h₁→Finset (Fin n) := fun j => NormalizedNetwork.rowSupport (net.A j)

/-- The literal good event for all original first rows implies ActualClean
for every actual second neuron, with the original tail enumeration and order. -/
theorem good_implies_actualClean {h₁ h₂ : ℕ}
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (S : Finset (Fin n)) (K : ℕ) (r : Fin h₂)
    (τ ρ : Equiv.Perm (Fin (tailCount S)))
    (hgood : (τ,ρ)∉familyBadConfigurations (firstSupports net) S K) :
    ActualClean net (tail S) r ρ K τ := by
  intro j _ hs g hg
  exact family_good_excludes_dominant net.A hn.1 S τ ρ K hgood j hs g hg

#print axioms dominant_isolated_support_bad
#print axioms good_event_excludes_nonbraid_dominant
#print axioms family_good_excludes_dominant
#print axioms good_implies_actualClean
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
