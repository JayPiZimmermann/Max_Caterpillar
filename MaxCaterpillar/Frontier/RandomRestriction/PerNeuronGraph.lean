import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronModel
import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronMatching

/-! # Actual ambient braid graph coefficients in the local matching -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
open BigOperators Configurations
variable {m h₁ h₂ : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] braidGraphDecidable

theorem baseTail_eq_tailLabelEmbedding (σ : FullPerm m) :
    baseTail σ=GraphRestriction.tailLabelEmbedding σ := by
  apply Function.Embedding.ext
  intro i
  rfl

/-- The graph count is precisely the number of nonzero actual braid columns.
Distinctness is derived from the actual matching slot embedding. -/
theorem native_braid_matchingCount_eq
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (k : Fin h₂) (e : Fin m ↪ Fin (m+5)) (slot : (ι×Bool) ↪ Fin m)
    (τ : TailPerm m) :
    nativeMatchingCount ((braidInteractionGraph net hn k).comap e) slot τ =
      (Finset.univ.filter fun i => braidEdgeWeight net.A (net.W k)
        (e (τ (slot (i,false)))) (e (τ (slot (i,true)))) ≠ 0).card := by
  classical
  unfold nativeMatchingCount
  congr 1
  ext i
  have hne : e (τ (slot (i,false))) ≠ e (τ (slot (i,true))) :=
    e.injective.ne (τ.injective.ne (Matching.slot_pair_ne slot i))
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,
    SimpleGraph.comap_adj,braidInteractionGraph_adj,hne,true_and]
  exact and_iff_right hne

theorem tail_braidGraph_edge_lower_bound
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (k : Fin h₂) (σ : FullPerm m) :
    ((braidInteractionGraph net hn k).edgeFinset.card : ℝ)-5*((m:ℝ)+4) ≤
      (((braidInteractionGraph net hn k).comap (baseTail σ)).edgeFinset.card : ℝ) := by
  classical
  rw [baseTail_eq_tailLabelEmbedding]
  exact GraphRestriction.tailGraph_edge_lower_bound _ σ

end MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
