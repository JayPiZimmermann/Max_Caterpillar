import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventPlacements
import MaxCaterpillar.Frontier.RandomRestriction.UniformTuplesRoles

/-! Literal growing-arity support bad events. All witnesses are four distinct
original support labels; event definitions contain no counting conclusion. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEvent
open GoodEventPlacements
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent (ACRole BRole smallRankGaps)
variable {m : ℕ}

noncomputable def roleEvents {n : ℕ} {κ : Type*} [Fintype κ]
    (e : κ→(Fin 4↪Fin n)) (B : Finset (Fin 4↪Fin n)) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.biUnion fun r => UniformTuples.event (e r) B

noncomputable def supportBadAt (k : ℕ) (T : Finset (Fin (m+k)))
    (Γ : Finset (Fin m)) : Finset (Equiv.Perm (Fin (m+k))) :=
  (roleEvents (fun r : ACRole T => r.embedding) (fullCaseA k Γ) ∪
    roleEvents (fun r : BRole T => r.embedding) (fullCaseB k Γ)) ∪
    roleEvents (fun r : ACRole T => r.embedding) (fullCaseC k Γ)

noncomputable def supportBadConfigurations (k : ℕ) (T : Finset (Fin (m+k)))
    (K : ℕ) : Finset (Equiv.Perm (Fin (m+k))×Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter fun p => p.1∈supportBadAt k T (smallRankGaps p.2 K)

@[simp] theorem mem_roleEvents {n : ℕ} {κ : Type*} [Fintype κ]
    (e : κ→(Fin 4↪Fin n)) (B : Finset (Fin 4↪Fin n)) (σ : Equiv.Perm (Fin n)) :
    σ∈roleEvents e B ↔ ∃r,UniformTuples.induced (e r) σ∈B := by
  classical
  simp only [roleEvents,Finset.mem_biUnion,Finset.mem_univ,true_and,UniformTuples.mem_event]

theorem mem_supportBadAt (k : ℕ) (T : Finset (Fin (m+k))) (Γ : Finset (Fin m))
    (σ : Equiv.Perm (Fin (m+k))) :
    σ∈supportBadAt k T Γ ↔
      (∃r : ACRole T,UniformTuples.induced r.embedding σ∈fullCaseA k Γ) ∨
      (∃r : BRole T,UniformTuples.induced r.embedding σ∈fullCaseB k Γ) ∨
      (∃r : ACRole T,UniformTuples.induced r.embedding σ∈fullCaseC k Γ) := by
  classical
  simp only [supportBadAt,Finset.mem_union,mem_roleEvents,or_assoc]

theorem mem_supportBadAt_of_caseA (k : ℕ) (T : Finset (Fin (m+k)))
    (Γ : Finset (Fin m)) (σ : Equiv.Perm (Fin (m+k))) (r : ACRole T)
    (h : UniformTuples.induced r.embedding σ∈fullCaseA k Γ) : σ∈supportBadAt k T Γ :=
  (mem_supportBadAt k T Γ σ).mpr (Or.inl ⟨r,h⟩)

theorem mem_supportBadAt_of_caseB (k : ℕ) (T : Finset (Fin (m+k)))
    (Γ : Finset (Fin m)) (σ : Equiv.Perm (Fin (m+k))) (r : BRole T)
    (h : UniformTuples.induced r.embedding σ∈fullCaseB k Γ) : σ∈supportBadAt k T Γ :=
  (mem_supportBadAt k T Γ σ).mpr (Or.inr (Or.inl ⟨r,h⟩))

theorem mem_supportBadAt_of_caseC (k : ℕ) (T : Finset (Fin (m+k)))
    (Γ : Finset (Fin m)) (σ : Equiv.Perm (Fin (m+k))) (r : ACRole T)
    (h : UniformTuples.induced r.embedding σ∈fullCaseC k Γ) : σ∈supportBadAt k T Γ :=
  (mem_supportBadAt k T Γ σ).mpr (Or.inr (Or.inr ⟨r,h⟩))

@[simp] theorem mem_supportBadConfigurations (k : ℕ) (T : Finset (Fin (m+k)))
    (K : ℕ) (p : Equiv.Perm (Fin (m+k))×Equiv.Perm (Fin m)) :
    p∈supportBadConfigurations k T K ↔p.1∈supportBadAt k T (smallRankGaps p.2 K) := by
  classical
  simp only [supportBadConfigurations,Finset.mem_filter,Finset.mem_univ,true_and]

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEvent
