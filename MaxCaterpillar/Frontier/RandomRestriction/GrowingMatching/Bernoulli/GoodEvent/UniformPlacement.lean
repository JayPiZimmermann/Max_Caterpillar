import MaxCaterpillar.Frontier.RandomRestriction.UniformTuples

/-! # Actual uniform placements of fixed original labels in a tail

The event is a literal existential placement into the original tail embedding.
A tuple which does not factor through the tail cannot occur. Otherwise inverse
permutation transports the event to the previously proved uniform tuple law.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
open BigOperators
variable {n m d : ℕ}

noncomputable def placementEvent (e : Fin m ↪ Fin n) (q : Fin d ↪ Fin n)
    (B : Finset (Fin d ↪ Fin m)) : Finset (Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter fun τ => ∃ a∈B,∀ i,e (τ (a i))=q i

@[simp] theorem mem_placementEvent (e : Fin m ↪ Fin n) (q : Fin d ↪ Fin n)
    (B : Finset (Fin d ↪ Fin m)) (τ : Equiv.Perm (Fin m)) :
    τ∈placementEvent e q B ↔ ∃ a∈B,∀ i,e (τ (a i))=q i := by
  classical
  simp only [placementEvent,Finset.mem_filter,Finset.mem_univ,true_and]

/-- If the original tuple is a tail tuple, its actual placement is read from
an inverse permutation, rather than assuming the tail placement uniform. -/
theorem mem_placementEvent_iff_inverse (e : Fin m ↪ Fin n) (q : Fin d ↪ Fin n)
    (B : Finset (Fin d ↪ Fin m)) (f : Fin d ↪ Fin m)
    (hf : ∀ i,e (f i)=q i) (τ : Equiv.Perm (Fin m)) :
    τ∈placementEvent e q B ↔ UniformTuples.induced f τ.symm∈B := by
  classical
  rw [mem_placementEvent]
  constructor
  · rintro ⟨a,ha,he⟩
    have heq : UniformTuples.induced f τ.symm=a := by
      apply Function.Embedding.ext
      intro i
      apply τ.injective
      change τ (τ.symm (f i))=τ (a i)
      rw [Equiv.apply_symm_apply]
      apply e.injective
      exact (hf i).trans (he i).symm
    rw [heq]
    exact ha
  · intro h
    exact ⟨UniformTuples.induced f τ.symm,h,fun i=>by
      change e (τ (τ.symm (f i)))=q i
      rw [Equiv.apply_symm_apply,hf]⟩

/-- Inversion is a genuine bijection of the complete permutation sample. -/
theorem placementEvent_card_eq (e : Fin m ↪ Fin n) (q : Fin d ↪ Fin n)
    (B : Finset (Fin d ↪ Fin m)) (f : Fin d ↪ Fin m)
    (hf : ∀ i,e (f i)=q i) :
    (placementEvent e q B).card=(UniformTuples.event f B).card := by
  classical
  apply Finset.card_congr (fun τ _=>τ.symm)
  · intro τ hτ
    exact (UniformTuples.mem_event f B τ.symm).mpr
      ((mem_placementEvent_iff_inverse e q B f hf τ).mp hτ)
  · intro τ υ _ _ h
    have hh := congrArg (fun f : Equiv.Perm (Fin m) => f.symm) h
    simpa only [Equiv.symm_symm] using hh
  · intro τ hτ
    refine ⟨τ.symm,?_,Equiv.symm_symm τ⟩
    apply (mem_placementEvent_iff_inverse e q B f hf τ.symm).mpr
    simpa only [Equiv.symm_symm] using (UniformTuples.mem_event f B τ).mp hτ

theorem placementEvent_empty_of_no_factor (e : Fin m ↪ Fin n) (q : Fin d ↪ Fin n)
    (B : Finset (Fin d ↪ Fin m))
    (hn : ¬∃ f : Fin d ↪ Fin m,∀ i,e (f i)=q i) : placementEvent e q B=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro τ hτ
  obtain ⟨a,_,ha⟩ := (mem_placementEvent e q B τ).mp hτ
  exact hn ⟨a.trans τ.toEmbedding,ha⟩

/-- Every original-label placement event has at most the uniform distinct-tuple
mass. This also covers empty or undersized tails without added hypotheses. -/
theorem placementEvent_fraction_le (e : Fin m ↪ Fin n) (q : Fin d ↪ Fin n)
    (B : Finset (Fin d ↪ Fin m)) :
    ((placementEvent e q B).card : ℝ)/Fintype.card (Equiv.Perm (Fin m)) ≤
      (B.card : ℝ)/(m.descFactorial d : ℝ) := by
  classical
  by_cases h : ∃ f : Fin d ↪ Fin m,∀ i,e (f i)=q i
  · obtain ⟨f,hf⟩ := h
    rw [placementEvent_card_eq e q B f hf,UniformTuples.real_fraction_eq]
  · rw [placementEvent_empty_of_no_factor e q B h,Finset.card_empty,Nat.cast_zero,zero_div]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

#print axioms placementEvent_card_eq
#print axioms placementEvent_fraction_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
