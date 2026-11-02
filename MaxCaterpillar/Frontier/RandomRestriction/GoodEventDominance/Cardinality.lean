import MaxCaterpillar.Frontier.RandomRestriction.GoodEventMembership

/-! # Every counted support bad event uses at least four actual labels -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
open GoodEvent

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
theorem support_bad_requires_card_four {m : ℕ} (T : Finset (Fin (m+5)))
    (Γ : Finset (Fin m)) (τ : Equiv.Perm (Fin (m+5)))
    (h : τ∈supportBadAt T Γ) : 4≤T.card := by
  rcases (mem_supportBadAt T Γ τ).mp h with ⟨r,_⟩ | ⟨r,_⟩ | ⟨r,_⟩
  · exact four_le_of_supported_embedding T r.embedding r.embedding_mem_support
  · exact four_le_of_supported_embedding T r.embedding r.embedding_mem_support
  · exact four_le_of_supported_embedding T r.embedding r.embedding_mem_support

/-- The same cardinality obstruction holds for the literal full configuration. -/
theorem support_bad_configuration_requires_card_four {m : ℕ}
    (T : Finset (Fin (m+5))) (K : ℕ)
    (p : Equiv.Perm (Fin (m+5)) × Equiv.Perm (Fin m))
    (h : p∈supportBadConfigurations T K) : 4≤T.card :=
  support_bad_requires_card_four T (smallRankGaps p.2 K) p.1
    ((mem_supportBadConfigurations T K p).mp h)

#print axioms support_bad_requires_card_four
#print axioms support_bad_configuration_requires_card_four
end MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
