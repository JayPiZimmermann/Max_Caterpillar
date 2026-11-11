import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.Cardinality
set_option autoImplicit false
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEvent
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance

example {m : ℕ} (k : ℕ) (T : Finset (Fin (m+k))) (Γ : Finset (Fin m))
    (τ : Equiv.Perm (Fin (m+k))) (h : τ∈supportBadAt k T Γ) : 4≤T.card :=
  support_bad_requires_card_four k T Γ τ h
example {m : ℕ} (k : ℕ) (T : Finset (Fin (m+k))) (K : ℕ)
    (p : Equiv.Perm (Fin (m+k)) × Equiv.Perm (Fin m))
    (h : p∈supportBadConfigurations k T K) : 4≤T.card :=
  support_bad_configuration_requires_card_four k T K p h
example {m : ℕ} (k : ℕ) (T : Finset (Fin (m+k))) (Γ : Finset (Fin m))
    (τ : Equiv.Perm (Fin (m+k))) (hT : T.card=3) : τ∉supportBadAt k T Γ := by
  intro h
  have hc := support_bad_requires_card_four k T Γ τ h
  rw [hT] at hc
  exact (by decide : ¬(4 : ℕ)≤3) hc
example {m : ℕ} (k : ℕ) (T : Finset (Fin (m+k))) (K : ℕ)
    (p : Equiv.Perm (Fin (m+k)) × Equiv.Perm (Fin m)) (hT : T.card≤3) :
    p∉supportBadConfigurations k T K := by
  intro h
  exact (by decide : ¬(4 : ℕ)≤3)
    (le_trans (support_bad_configuration_requires_card_four k T K p h) hT)

/-- No selected-arity nonemptiness premise is hidden in the public statement. -/
example {m : ℕ} (T : Finset (Fin (m+0))) (Γ : Finset (Fin m))
    (τ : Equiv.Perm (Fin (m+0))) (h : τ∈supportBadAt 0 T Γ) : 4≤T.card :=
  support_bad_requires_card_four 0 T Γ τ h
example {m : ℕ} (T : Finset (Fin (m+1))) (K : ℕ)
    (p : Equiv.Perm (Fin (m+1)) × Equiv.Perm (Fin m))
    (h : p∈supportBadConfigurations 1 T K) : 4≤T.card :=
  support_bad_configuration_requires_card_four 1 T K p h

#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.support_bad_requires_card_four
#print axioms MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance.support_bad_configuration_requires_card_four
