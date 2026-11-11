import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventProbability

/-! # The actual family good event excludes every nonbraid dominant slot

The finite row family may be the original feeding-row subtype. These are
semantic implications of the literal finite union event; no probability bound
or abstract cleanliness predicate is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance
open BigOperators Cartesian DominantGap GoodEvent
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent (isolatedGaps smallRankGaps)
variable {m : ℕ} {ι : Type*} [Fintype ι]

theorem feeding_good_excludes_nonbraid_dominant (k : ℕ)
    (w : ι→Point (m+k)) (hzero : ∀ j,(∑ i,w j i)=0)
    (τ : Equiv.Perm (Fin (m+k))) (ρ : Equiv.Perm (Fin m)) (K : ℕ)
    (hgood : (τ,ρ)∉feedingBadConfigurations k (fun j => NormalizedNetwork.rowSupport (w j)) K)
    (j : ι) (hsupport : 3≤(NormalizedNetwork.rowSupport (w j)).card)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps ρ K)) :
    ¬GapDominant (positionConfig ρ) (collapsedRow k τ (w j)) g := by
  apply good_event_excludes_nonbraid_dominant k (w j) (hzero j) hsupport τ ρ K ?_ g hg
  intro hbad
  exact hgood ((mem_feedingBadConfigurations k (fun j => NormalizedNetwork.rowSupport (w j)) K
    (τ,ρ)).mpr ⟨j,hbad⟩)

theorem feeding_good_excludes_nonbraid_dominant_of_tail_order (k : ℕ)
    (w : ι→Point (m+k)) (hzero : ∀ j,(∑ i,w j i)=0)
    (τ : Equiv.Perm (Fin (m+k))) (p : RawConfig m) (v : ι→Option (Fin m)→ℝ)
    (htail : ∀ j t,v j (some (p.1 t))=tailWeight k τ (w j) t)
    (K : ℕ)
    (hgood : (τ,p.2)∉feedingBadConfigurations k (fun j => NormalizedNetwork.rowSupport (w j)) K)
    (j : ι) (hsupport : 3≤(NormalizedNetwork.rowSupport (w j)).card)
    (g : Fin m) (hg : g∈isolatedGaps (smallRankGaps p.2 K)) : ¬GapDominant p (v j) g := by
  apply good_event_excludes_nonbraid_dominant_of_tail_order k (w j) (hzero j) hsupport
    τ p (v j) (htail j) K ?_ g hg
  intro hbad
  exact hgood ((mem_feedingBadConfigurations k (fun j => NormalizedNetwork.rowSupport (w j)) K
    (τ,p.2)).mpr ⟨j,hbad⟩)

#print axioms feeding_good_excludes_nonbraid_dominant
#print axioms feeding_good_excludes_nonbraid_dominant_of_tail_order
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance
