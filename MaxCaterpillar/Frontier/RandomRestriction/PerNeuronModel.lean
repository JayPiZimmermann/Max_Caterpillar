import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronScale
import MaxCaterpillar.Frontier.RandomRestriction.ActualClean
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesProbability
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.NativeEvent
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Graph

/-! # The literal actual per-neuron event

The three independent permutations select the tied block, order its complement,
and rank the gaps. Survival is evaluated at the actual original-coordinate
network point. The counted good event implies the clean condition used by the
local fair-coin argument; this implication is proved below.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
open BigOperators Configurations DominantGap GoodEvent
variable {m h₁ h₂ : ℕ}

noncomputable def braidGraphDecidable (net : NormalizedNetwork (m+5) h₁ h₂)
    (hn : net.TranslationNormalized) (k : Fin h₂) :
    DecidableRel (braidInteractionGraph net hn k).Adj := Classical.decRel _
attribute [local instance] braidGraphDecidable

noncomputable def firstSupports (net : NormalizedNetwork (m+5) h₁ h₂) :
    Fin h₁ → Finset (Fin (m+5)) := fun j => NormalizedNetwork.rowSupport (net.A j)

noncomputable def actualPoint (ω : Configuration m) (T : ℝ) : Point (m+5) :=
  actualGapPoint (baseTail ω.1) (ω.2.1,ω.2.2) T

/-- A concrete event, with no probability estimate included in its definition. -/
noncomputable def neuronEvent (net : NormalizedNetwork (m+5) h₁ h₂)
    (hn : net.TranslationNormalized) (K : ℕ) (T : ℝ) (k : Fin h₂) :
    Finset (Configuration m) := by
  classical
  exact Finset.univ.filter fun ω =>
    ω ∉ feedingBadConfigurationsThree (firstSupports net) K ∧
    ω.2.2 ∉ badIsolatedEvent m K ∧
    net.inner k (actualPoint ω T)=0 ∧
    GraphRestriction.hasTwoDisjointSelectedEdges (braidInteractionGraph net hn k) ω.1

@[simp] theorem mem_neuronEvent (net : NormalizedNetwork (m+5) h₁ h₂)
    (hn : net.TranslationNormalized) (K : ℕ) (T : ℝ) (k : Fin h₂)
    (ω : Configuration m) :
    ω ∈ neuronEvent net hn K T k ↔
      ω ∉ feedingBadConfigurationsThree (firstSupports net) K ∧
      ω.2.2 ∉ badIsolatedEvent m K ∧
      net.inner k (actualPoint ω T)=0 ∧
      GraphRestriction.hasTwoDisjointSelectedEdges (braidInteractionGraph net hn k) ω.1 := by
  classical
  simp only [neuronEvent,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The actual counted good event excludes all feeding nonbraid dominant
rows at the actual isolated matching slots. -/
theorem good_implies_actualClean (net : NormalizedNetwork (m+5) h₁ h₂)
    (hn : net.TranslationNormalized) (K : ℕ) (k : Fin h₂)
    (σ : FullPerm m) (τ : TailPerm m) (ρ : RankPerm m)
    (hgood : (σ,τ,ρ) ∉ feedingBadConfigurationsThree (firstSupports net) K) :
    ActualClean net (baseTail σ) k ρ K τ := by
  classical
  intro j hW hs g hg
  have hgoodj : (effectivePermutation σ τ,ρ) ∉
      supportBadConfigurations (NormalizedNetwork.rowSupport (net.A j)) K := by
    intro hj
    apply hgood
    apply (mem_pullbackEvent _ _).mpr
    change effectiveConfiguration (σ,τ,ρ) ∈
      feedingBadConfigurations (firstSupports net) K
    apply Finset.mem_biUnion.mpr
    exact ⟨j,Finset.mem_univ _,hj⟩
  apply GoodEventDominance.good_event_excludes_nonbraid_dominant_of_tail_order
    (net.A j) (hn.1 j) hs (effectivePermutation σ τ) (τ,ρ)
    (DominantGap.collapsedRow (baseTail σ) (net.A j)) ?_ K hgoodj g hg
  intro a
  change net.A j (baseTail σ (τ a)) =
    net.A j ((effectivePermutation σ τ).symm (tailPosition m a))
  rw [effectivePermutation_tail]
  rfl

end MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
