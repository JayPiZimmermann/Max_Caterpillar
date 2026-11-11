import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Semantics
set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier.RandomRestriction
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent (isolatedGaps smallRankGaps)

example {n : ℕ} (S : Finset (Fin n)) (w : Point n)
    (h : DominantGap.collapsedRow (Sampling.tail S) w none≠0) :
    ∃s∈S,w s≠0 := selected_nonzero_of_anchor_nonzero S w h
example {n : ℕ} (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (w : Point n) (a b : Fin (Sampling.tailCount S))
    (h : 3≤(NormalizedNetwork.rowSupport w).card)
    (honly : ∀t,tailWeight S τ w t≠0→t=a∨t=b) :
    ∃s∈S,w s≠0 := selected_nonzero_of_support_three S τ w a b h honly
example {n : ℕ} (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (w : Point n) (a b : Fin (Sampling.tailCount S)) (hab : a≠b) (hw : (∑i,w i)=0)
    (hpair : tailWeight S τ w a+tailWeight S τ w b=0)
    (honly : ∀t,tailWeight S τ w t≠0→t=a∨t=b) :
    (∑s in S,w s)=0 := selected_sum_zero_of_only_opposite_pair S τ w a b hab hw hpair honly

example {n : ℕ} (S : Finset (Fin n)) (w : Point n) (hzero : (∑i,w i)=0)
    (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ ρ : Equiv.Perm (Fin (Sampling.tailCount S))) (K : ℕ) (g : Fin (Sampling.tailCount S))
    (hdom : DominantGap.GapDominant (τ,ρ) (DominantGap.collapsedRow (Sampling.tail S) w) g)
    (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    (τ,ρ)∈supportBadConfigurations (NormalizedNetwork.rowSupport w) S K :=
  dominant_isolated_support_bad S w hzero hsupport τ ρ K g hdom hg

example {n : ℕ} (S : Finset (Fin n)) (w : Point n) (hzero : (∑i,w i)=0)
    (hsupport : 3≤(NormalizedNetwork.rowSupport w).card)
    (τ ρ : Equiv.Perm (Fin (Sampling.tailCount S))) (K : ℕ)
    (hgood : (τ,ρ)∉supportBadConfigurations (NormalizedNetwork.rowSupport w) S K)
    (g : Fin (Sampling.tailCount S)) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬DominantGap.GapDominant (τ,ρ) (DominantGap.collapsedRow (Sampling.tail S) w) g :=
  good_event_excludes_nonbraid_dominant S w hzero hsupport τ ρ K hgood g hg

example {n : ℕ} {κ : Type*} [Fintype κ] (rows : κ→Point n)
    (hzero : ∀j,(∑i,rows j i)=0) (S : Finset (Fin n))
    (τ ρ : Equiv.Perm (Fin (Sampling.tailCount S))) (K : ℕ)
    (hgood : (τ,ρ)∉familyBadConfigurations (fun j=>NormalizedNetwork.rowSupport (rows j)) S K)
    (j : κ) (hs : 3≤(NormalizedNetwork.rowSupport (rows j)).card)
    (g : Fin (Sampling.tailCount S)) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬DominantGap.GapDominant (τ,ρ) (DominantGap.collapsedRow (Sampling.tail S) (rows j)) g :=
  family_good_excludes_dominant rows hzero S τ ρ K hgood j hs g hg

example {n h₁ h₂ : ℕ} (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (S : Finset (Fin n)) (K : ℕ) (r : Fin h₂)
    (τ ρ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (hgood : (τ,ρ)∉familyBadConfigurations (fun j=>NormalizedNetwork.rowSupport (net.A j)) S K) :
    ActualClean net (Sampling.tail S) r ρ K τ := good_implies_actualClean net hn S K r τ ρ hgood

/-- The full-selected-set boundary has no tail slot; no positive-arity premise
is hidden in ActualClean or the canonical Sampling enumeration. -/
example {n h₁ h₂ : ℕ} (net : NormalizedNetwork n h₁ h₂) (r : Fin h₂) (K : ℕ) :
    ActualClean net (Sampling.tail (Finset.univ : Finset (Fin n))) r
      (Equiv.refl _) K (Equiv.refl _) := by
  intro j _ _ g _
  have hm : Sampling.tailCount (Finset.univ : Finset (Fin n))=0 := by simp [Sampling.tailCount]
  exact Fin.elim0 (Fin.cast hm g)

#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.selected_nonzero_of_anchor_nonzero
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.selected_nonzero_of_support_three
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.selected_sum_zero_of_only_opposite_pair
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.tail_supported
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.dominant_isolated_support_bad
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.good_event_excludes_nonbraid_dominant
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.family_good_excludes_dominant
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.good_implies_actualClean
