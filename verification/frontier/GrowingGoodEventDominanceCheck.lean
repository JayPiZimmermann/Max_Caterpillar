import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance

/-! Independent contracts on original real rows and literal counted events. -/
set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open Cartesian DominantGap GrowingMatching GrowingMatching.Configurations
open GrowingMatching.GoodEvent GrowingMatching.GoodEventDominance
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent (smallRankGaps isolatedGaps TailSameRun AnchorSameRun)
open MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance (dominant_prefix_cuts_zero nonzero_tail_has_run_partner)

example (k : ℕ) {m : ℕ} (w : Point (m+k)) (hw : (∑ i,w i)=0)
    (hs : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+k))) (ρ : Equiv.Perm (Fin m)) (K : ℕ) (g : Fin m)
    (hd : GapDominant (positionConfig ρ) (GrowingMatching.GoodEventDominance.collapsedRow k τ w) g)
    (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    (τ,ρ)∈supportBadConfigurations k (NormalizedNetwork.rowSupport w) K :=
  dominant_isolated_support_bad k w hw hs τ ρ K g hd hg

example (k : ℕ) {m : ℕ} (w : Point (m+k)) (hw : (∑ i,w i)=0)
    (hs : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+k))) (ρ : Equiv.Perm (Fin m)) (K : ℕ)
    (hgood : (τ,ρ)∉supportBadConfigurations k (NormalizedNetwork.rowSupport w) K)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬GapDominant (positionConfig ρ) (GrowingMatching.GoodEventDominance.collapsedRow k τ w) g :=
  good_event_excludes_nonbraid_dominant k w hw hs τ ρ K hgood g hg

example (k : ℕ) {m : ℕ} (w : Point (m+k)) (hw : (∑ i,w i)=0)
    (hs : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+k))) (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ j,v (some (p.1 j))=w (τ.symm (tailPosition k m j)))
    (K : ℕ) (g : Fin m) (hd : GapDominant p v g)
    (hg : g∈isolatedGaps (smallRankGaps p.2 K)) :
    (τ,p.2)∈supportBadConfigurations k (NormalizedNetwork.rowSupport w) K :=
  dominant_isolated_support_bad_of_tail_order k w hw hs τ p v htail K g hd hg

example (k : ℕ) {m : ℕ} (w : Point (m+k)) (hw : (∑ i,w i)=0)
    (hs : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+k))) (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ j,v (some (p.1 j))=w (τ.symm (tailPosition k m j)))
    (K : ℕ) (hgood : (τ,p.2)∉supportBadConfigurations k (NormalizedNetwork.rowSupport w) K)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps p.2 K)) : ¬GapDominant p v g :=
  good_event_excludes_nonbraid_dominant_of_tail_order k w hw hs τ p v htail K hgood g hg

example (k : ℕ) {m : ℕ} (w : Point (m+k)) (τ : Equiv.Perm (Fin (m+k))) :
    (∑ x : Option (Fin m),GrowingMatching.GoodEventDominance.collapsedRow k τ w x)=∑ i,w i :=
  collapsedRow_sum k τ w

example {m : ℕ} (p : RawConfig m) (v : Option (Fin m)→ℝ) (hv : (∑ x,v x)=0)
    (K : ℕ) (g : Fin m) (hd : GapDominant p v g) (hg : (p.2 g).val<K) :
    ∀ j∉smallRankGaps p.2 K,prefixCoeff p v j.val=0 := dominant_prefix_cuts_zero p v hv K g hd hg

example {m : ℕ} (p : RawConfig m) (v : Option (Fin m)→ℝ) (Γ : Finset (Fin m))
    (hv : (∑ x,v x)=0) (hcuts : ∀ j∉Γ,prefixCoeff p v j.val=0)
    (z : Fin m) (hz : v (some (p.1 z))≠0) :
    (∃ j,j≠z ∧ TailSameRun Γ z j ∧ v (some (p.1 j))≠0) ∨
      (AnchorSameRun Γ z ∧ v none≠0) := nonzero_tail_has_run_partner p v Γ hv hcuts z hz

example (k : ℕ) {m : ℕ} (τ : Equiv.Perm (Fin (m+k))) (w : Point (m+k)) (a b : Fin m)
    (hs : 3≤(NormalizedNetwork.rowSupport w).card)
    (ht : ∀ t : Fin m,tailWeight k τ w t≠0 → t=a ∨ t=b) :
    ∃ s : Fin k,selectedWeight k τ w s≠0 := selected_nonzero_of_support_three k τ w a b hs ht

example (k : ℕ) {m : ℕ} (w : Point (m+k)) (hw : (∑ i,w i)=0)
    (hs : (NormalizedNetwork.rowSupport w).card=3)
    (τ : Equiv.Perm (Fin (m+k))) (ρ : Equiv.Perm (Fin m)) (K : ℕ)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬GapDominant (positionConfig ρ) (GrowingMatching.GoodEventDominance.collapsedRow k τ w) g :=
  support_three_no_isolated_dominant k w hw hs τ ρ K g hg
example (k : ℕ) {m : ℕ} (w : Point (m+k)) (hw : (∑ i,w i)=0)
    (hs : (NormalizedNetwork.rowSupport w).card=3)
    (τ : Equiv.Perm (Fin (m+k))) (p : RawConfig m) (v : Option (Fin m)→ℝ)
    (htail : ∀ j,v (some (p.1 j))=w (τ.symm (tailPosition k m j)))
    (K : ℕ) (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps p.2 K)) : ¬GapDominant p v g :=
  support_three_no_isolated_dominant_of_tail_order k w hw hs τ p v htail K g hg

#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.collapsedRow_sum
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.selected_nonzero_of_support_three
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.selected_sum_zero_of_only_opposite_pair
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.dominant_prefix_cuts_zero
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.isolated_pair_prefix_values
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.isolated_pair_run_members
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.dominant_isolated_support_bad
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.good_event_excludes_nonbraid_dominant
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.tailCoefficient_eq_full_position_order
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.dominant_isolated_support_bad_of_tail_order
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.good_event_excludes_nonbraid_dominant_of_tail_order

#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.support_three_no_isolated_dominant
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.support_three_no_isolated_dominant_of_tail_order

example {m : ℕ} (w : Point (m+0)) (τ : Equiv.Perm (Fin (m+0))) :
    GrowingMatching.GoodEventDominance.collapsedRow 0 τ w none=0 := by
  simp only [GrowingMatching.GoodEventDominance.collapsedRow,Fin.sum_univ_zero]
example {m : ℕ} (w : Point (m+1)) (τ : Equiv.Perm (Fin (m+1))) :
    GrowingMatching.GoodEventDominance.collapsedRow 1 τ w none=selectedWeight 1 τ w 0 := by
  change (∑ s : Fin 1,selectedWeight 1 τ w s)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
example {m : ℕ} (w : Point (m+0)) (hw : (∑ i,w i)=0)
    (hs : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+0))) (ρ : Equiv.Perm (Fin m)) (K : ℕ) (g : Fin m)
    (hd : GapDominant (positionConfig ρ) (GrowingMatching.GoodEventDominance.collapsedRow 0 τ w) g)
    (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    (τ,ρ)∈supportBadConfigurations 0 (NormalizedNetwork.rowSupport w) K :=
  dominant_isolated_support_bad 0 w hw hs τ ρ K g hd hg
example {m : ℕ} (w : Point (m+1)) (hw : (∑ i,w i)=0)
    (hs : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ : Equiv.Perm (Fin (m+1))) (ρ : Equiv.Perm (Fin m)) (K : ℕ) (g : Fin m)
    (hd : GapDominant (positionConfig ρ) (GrowingMatching.GoodEventDominance.collapsedRow 1 τ w) g)
    (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    (τ,ρ)∈supportBadConfigurations 1 (NormalizedNetwork.rowSupport w) K :=
  dominant_isolated_support_bad 1 w hw hs τ ρ K g hd hg
