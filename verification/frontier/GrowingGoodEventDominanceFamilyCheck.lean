import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.Family
set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open Cartesian DominantGap GrowingMatching GrowingMatching.Configurations
open GrowingMatching.GoodEvent GrowingMatching.GoodEventDominance
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent (isolatedGaps smallRankGaps)

example {m : ℕ} {ι : Type*} [Fintype ι] (k : ℕ)
    (w : ι→Point (m+k)) (hzero : ∀ j,(∑ i,w j i)=0)
    (τ : Equiv.Perm (Fin (m+k))) (ρ : Equiv.Perm (Fin m)) (K : ℕ)
    (hgood : (τ,ρ)∉feedingBadConfigurations k (fun j => NormalizedNetwork.rowSupport (w j)) K)
    (j : ι) (hsupport : 3≤(NormalizedNetwork.rowSupport (w j)).card)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬GapDominant (positionConfig ρ) (GrowingMatching.GoodEventDominance.collapsedRow k τ (w j)) g :=
  feeding_good_excludes_nonbraid_dominant k w hzero τ ρ K hgood j hsupport g hg

example {m : ℕ} {ι : Type*} [Fintype ι] (k : ℕ)
    (w : ι→Point (m+k)) (hzero : ∀ j,(∑ i,w j i)=0)
    (τ : Equiv.Perm (Fin (m+k))) (p : RawConfig m) (v : ι→Option (Fin m)→ℝ)
    (htail : ∀ j t,v j (some (p.1 t))=w j (τ.symm (tailPosition k m t)))
    (K : ℕ)
    (hgood : (τ,p.2)∉feedingBadConfigurations k (fun j => NormalizedNetwork.rowSupport (w j)) K)
    (j : ι) (hsupport : 3≤(NormalizedNetwork.rowSupport (w j)).card)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps p.2 K)) : ¬GapDominant p (v j) g :=
  feeding_good_excludes_nonbraid_dominant_of_tail_order k w hzero τ p v htail K hgood j hsupport g hg

#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.feeding_good_excludes_nonbraid_dominant
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.feeding_good_excludes_nonbraid_dominant_of_tail_order
