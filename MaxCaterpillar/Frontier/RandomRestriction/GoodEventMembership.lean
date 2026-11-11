import MaxCaterpillar.Frontier.RandomRestriction.GoodEventProbability

/-! # Literal membership interfaces for the support bad event -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent

variable {m : ℕ}

@[simp] theorem mem_roleEvents {κ : Type*} [Fintype κ]
    (e : κ → (Fin 4 ↪ Fin (m + 5))) (B : Finset (Fin 4 ↪ Fin (m + 5)))
    (τ : Equiv.Perm (Fin (m + 5))) :
    τ ∈ roleEvents e B ↔ ∃ r, UniformTuples.induced (e r) τ ∈ B := by
  classical
  simp only [roleEvents, Finset.mem_biUnion, Finset.mem_univ, true_and, UniformTuples.mem_event]

theorem mem_supportBadAt (T : Finset (Fin (m + 5))) (Γ : Finset (Fin m))
    (τ : Equiv.Perm (Fin (m + 5))) :
    τ ∈ supportBadAt T Γ ↔
      (∃ r : ACRole T, UniformTuples.induced (ACRole.embedding r) τ ∈ fullCaseA Γ) ∨
      (∃ r : BRole T, UniformTuples.induced (BRole.embedding r) τ ∈ fullCaseB Γ) ∨
      (∃ r : ACRole T, UniformTuples.induced (ACRole.embedding r) τ ∈ fullCaseC Γ) := by
  classical
  simp only [supportBadAt, Finset.mem_union, mem_roleEvents, or_assoc]

theorem mem_supportBadAt_of_caseA (T : Finset (Fin (m + 5))) (Γ : Finset (Fin m))
    (τ : Equiv.Perm (Fin (m + 5))) (r : ACRole T)
    (h : UniformTuples.induced (ACRole.embedding r) τ ∈ fullCaseA Γ) :
    τ ∈ supportBadAt T Γ :=
  (mem_supportBadAt T Γ τ).mpr (Or.inl ⟨r, h⟩)

theorem mem_supportBadAt_of_caseB (T : Finset (Fin (m + 5))) (Γ : Finset (Fin m))
    (τ : Equiv.Perm (Fin (m + 5))) (r : BRole T)
    (h : UniformTuples.induced (BRole.embedding r) τ ∈ fullCaseB Γ) :
    τ ∈ supportBadAt T Γ :=
  (mem_supportBadAt T Γ τ).mpr (Or.inr (Or.inl ⟨r, h⟩))

theorem mem_supportBadAt_of_caseC (T : Finset (Fin (m + 5))) (Γ : Finset (Fin m))
    (τ : Equiv.Perm (Fin (m + 5))) (r : ACRole T)
    (h : UniformTuples.induced (ACRole.embedding r) τ ∈ fullCaseC Γ) :
    τ ∈ supportBadAt T Γ :=
  (mem_supportBadAt T Γ τ).mpr (Or.inr (Or.inr ⟨r, h⟩))

@[simp] theorem mem_supportBadConfigurations (T : Finset (Fin (m + 5))) (K : ℕ)
    (p : Equiv.Perm (Fin (m + 5)) × Equiv.Perm (Fin m)) :
    p ∈ supportBadConfigurations T K ↔ p.1 ∈ supportBadAt T (smallRankGaps p.2 K) := by
  classical
  simp only [supportBadConfigurations, Finset.mem_filter, Finset.mem_univ, true_and]

end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
