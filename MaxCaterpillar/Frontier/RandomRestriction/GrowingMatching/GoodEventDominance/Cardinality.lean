import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventMembership

/-! # Every growing-arity support bad event uses four actual labels -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEvent
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent (smallRankGaps)

private theorem four_le_of_supported_embedding {α : Type*} [DecidableEq α]
    (T : Finset α) (e : Fin 4 ↪ α) (hmem : ∀ i,e i∈T) : 4≤T.card := by
  classical
  have hsub : (Finset.univ.image e) ⊆ T := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact hmem i
  have hc := Finset.card_le_of_subset hsub
  rw [Finset.card_image_of_injective _ e.injective,Finset.card_univ,Fintype.card_fin] at hc
  exact hc

/-- A/C and B roles each supply four distinct labels of the actual support. -/
theorem support_bad_requires_card_four {m : ℕ} (k : ℕ) (T : Finset (Fin (m+k)))
    (Γ : Finset (Fin m)) (τ : Equiv.Perm (Fin (m+k)))
    (h : τ∈supportBadAt k T Γ) : 4≤T.card := by
  rcases (mem_supportBadAt k T Γ τ).mp h with ⟨r,_⟩ | ⟨r,_⟩ | ⟨r,_⟩
  · exact four_le_of_supported_embedding T r.embedding r.embedding_mem_support
  · exact four_le_of_supported_embedding T r.embedding r.embedding_mem_support
  · exact four_le_of_supported_embedding T r.embedding r.embedding_mem_support

/-- The same cardinality obstruction holds for the literal full configuration. -/
theorem support_bad_configuration_requires_card_four {m : ℕ}
    (k : ℕ) (T : Finset (Fin (m+k))) (K : ℕ)
    (p : Equiv.Perm (Fin (m+k)) × Equiv.Perm (Fin m))
    (h : p∈supportBadConfigurations k T K) : 4≤T.card :=
  support_bad_requires_card_four k T (smallRankGaps p.2 K) p.1
    ((mem_supportBadConfigurations k T K p).mp h)

#print axioms support_bad_requires_card_four
#print axioms support_bad_configuration_requires_card_four
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance
