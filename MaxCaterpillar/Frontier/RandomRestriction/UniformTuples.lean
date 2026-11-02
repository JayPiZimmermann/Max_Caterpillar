import Mathlib
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fintype

/-! # Actual uniform ordered distinct tuples induced by uniform permutations

Fix any injection of labels into a finite ground set. Composing those labels
with every ground-set permutation gives every injective ordered tuple equally
often. The proof extends the finite bijection between two tuple ranges to an
actual global permutation; no distributional hypothesis is introduced.
-/
set_option autoImplicit false
open scoped BigOperators
namespace MaxCaterpillar.Frontier.RandomRestriction.UniformTuples

variable {d m : ℕ}

/-- The actual ordered distinct tuple read from a global permutation. -/
def induced (e : Fin d ↪ Fin m) (τ : Equiv.Perm (Fin m)) : Fin d ↪ Fin m :=
  e.trans τ.toEmbedding

@[simp] theorem induced_apply (e : Fin d ↪ Fin m) (τ : Equiv.Perm (Fin m))
    (i : Fin d) : induced e τ i = τ (e i) := rfl

/-- Any two injective tuples are related by a permutation of the whole ground
set, including the empty-ground-set and full-tuple cases. -/
theorem exists_permutation_between (a b : Fin d ↪ Fin m) :
    ∃ π : Equiv.Perm (Fin m), ∀ i, π (a i) = b i := by
  classical
  let r : Set.range a ≃ Set.range b := a.toEquivRange.symm.trans b.toEquivRange
  refine ⟨r.extendSubtype,?_⟩
  intro i
  rw [Equiv.extendSubtype_apply_of_mem r (a i) ⟨i,rfl⟩]
  change (b.toEquivRange (a.toEquivRange.symm ⟨a i,⟨i,rfl⟩⟩)).val = b i
  have hh : (⟨a i,⟨i,rfl⟩⟩ : Set.range a) = a.toEquivRange i := rfl
  rw [hh,Equiv.symm_apply_apply]
  rfl

noncomputable def fiber (e a : Fin d ↪ Fin m) : Finset (Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter fun τ => induced e τ = a

@[simp] theorem mem_fiber (e a : Fin d ↪ Fin m) (τ : Equiv.Perm (Fin m)) :
    τ ∈ fiber e a ↔ induced e τ = a := by
  classical
  simp [fiber]

/-- Left composition by a genuine ground-set permutation bijects tuple fibers. -/
theorem card_fiber_eq (e a b : Fin d ↪ Fin m) : (fiber e a).card = (fiber e b).card := by
  classical
  obtain ⟨π,hπ⟩ := exists_permutation_between a b
  apply Finset.card_congr (fun τ _ => τ.trans π)
  · intro τ hτ
    apply (mem_fiber e b (τ.trans π)).mpr
    apply Function.Embedding.ext
    intro i
    have hh := congrArg (fun c : Fin d ↪ Fin m => c i) ((mem_fiber e a τ).mp hτ)
    change τ (e i) = a i at hh
    change π (τ (e i)) = b i
    rw [hh,hπ]
  · intro τ σ _ _ he
    apply Equiv.ext
    intro x
    exact π.injective (congrArg (fun q : Equiv.Perm (Fin m) => q x) he)
  · intro σ hσ
    refine ⟨σ.trans π.symm,?_,?_⟩
    · apply (mem_fiber e a (σ.trans π.symm)).mpr
      apply Function.Embedding.ext
      intro i
      have hh := congrArg (fun c : Fin d ↪ Fin m => c i) ((mem_fiber e b σ).mp hσ)
      change σ (e i) = b i at hh
      change π.symm (σ (e i)) = a i
      rw [hh,←hπ i,Equiv.symm_apply_apply]
    · ext x
      simp

/-- A bad event is any finite set of injective tuples; this is its literal
preimage inside all global permutations. -/
noncomputable def event (e : Fin d ↪ Fin m) (B : Finset (Fin d ↪ Fin m)) :
    Finset (Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter fun τ => induced e τ ∈ B

@[simp] theorem mem_event (e : Fin d ↪ Fin m) (B : Finset (Fin d ↪ Fin m))
    (τ : Equiv.Perm (Fin m)) : τ ∈ event e B ↔ induced e τ ∈ B := by
  classical
  simp [event]

/-- Exact finite count before any division. -/
theorem card_event (e : Fin d ↪ Fin m) (B : Finset (Fin d ↪ Fin m)) :
    (event e B).card = B.card * (fiber e e).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := induced e) (t := B)
    (fun τ hτ => (mem_event e B τ).mp hτ)]
  have hh : ∀ a ∈ B, ((event e B).filter fun τ => induced e τ = a).card =
      (fiber e e).card := by
    intro a ha
    have he : (event e B).filter (fun τ => induced e τ = a) = fiber e a := by
      ext τ
      simp only [Finset.mem_filter,mem_event,mem_fiber]
      exact ⟨fun h => h.2,fun h => ⟨h ▸ ha,h⟩⟩
    rw [he,card_fiber_eq e a e]
  calc
    (∑ a in B, ((event e B).filter fun τ => induced e τ = a).card) =
        ∑ _a in B, (fiber e e).card := Finset.sum_congr rfl hh
    _ = B.card * (fiber e e).card := by simp

/-- All permutation fibers together give the literal permutation-space size. -/
theorem card_permutations (e : Fin d ↪ Fin m) :
    Fintype.card (Equiv.Perm (Fin m)) =
      Fintype.card (Fin d ↪ Fin m) * (fiber e e).card := by
  classical
  have hh := card_event e (Finset.univ : Finset (Fin d ↪ Fin m))
  have he : event e Finset.univ = Finset.univ := by
    ext τ
    simp only [mem_event,Finset.mem_univ]
  rw [he,Finset.card_univ,Finset.card_univ] at hh
  exact hh

/-- The exact cross-multiplied uniform law, with natural-number counts. -/
theorem card_event_mul_tuple_card (e : Fin d ↪ Fin m) (B : Finset (Fin d ↪ Fin m)) :
    (event e B).card * Fintype.card (Fin d ↪ Fin m) =
      B.card * Fintype.card (Equiv.Perm (Fin m)) := by
  rw [card_event,card_permutations e]
  ring

/-- Number of ordered distinct d-tuples from an m-element ground set. -/
theorem card_tuples : Fintype.card (Fin d ↪ Fin m) = m.descFactorial d := by
  simp only [Fintype.card_embedding_eq,Fintype.card_fin]

/-- The fixed injection supplies precisely the nonempty-space condition; no
extra positive-size hypothesis is needed, even when d=m=0. -/
theorem tuple_count_pos (e : Fin d ↪ Fin m) : 0 < m.descFactorial d := by
  rw [←card_tuples]
  exact Fintype.card_pos_iff.mpr ⟨e⟩

/-- Uniform probability is the actual number of favorable global permutations
divided by the actual number of all global permutations. -/
noncomputable def fraction (e : Fin d ↪ Fin m) (B : Finset (Fin d ↪ Fin m)) : ℚ :=
  (event e B).card / (Fintype.card (Equiv.Perm (Fin m)) : ℚ)

/-- A uniform global permutation induces a genuinely uniform ordered distinct
tuple. The event B is arbitrary and no uniform-law assumption is present. -/
theorem fraction_eq (e : Fin d ↪ Fin m) (B : Finset (Fin d ↪ Fin m)) :
    fraction e B = (B.card : ℚ) / (m.descFactorial d : ℚ) := by
  have hp : (Fintype.card (Equiv.Perm (Fin m)) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin m)⟩).ne'
  have ht : (m.descFactorial d : ℚ) ≠ 0 := by
    exact_mod_cast (tuple_count_pos e).ne'
  apply (div_eq_div_iff hp ht).mpr
  rw [←card_tuples]
  exact_mod_cast card_event_mul_tuple_card e B

/-- The same exact law as a real-valued fraction for expectation bounds. -/
theorem real_fraction_eq (e : Fin d ↪ Fin m) (B : Finset (Fin d ↪ Fin m)) :
    ((event e B).card : ℝ) / (Fintype.card (Equiv.Perm (Fin m)) : ℝ) =
      (B.card : ℝ) / (m.descFactorial d : ℝ) := by
  have hp : (Fintype.card (Equiv.Perm (Fin m)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin m)⟩).ne'
  have ht : (m.descFactorial d : ℝ) ≠ 0 := by
    exact_mod_cast (tuple_count_pos e).ne'
  apply (div_eq_div_iff hp ht).mpr
  rw [←card_tuples]
  exact_mod_cast card_event_mul_tuple_card e B

@[simp] theorem fraction_empty (e : Fin d ↪ Fin m) : fraction e ∅ = 0 := by
  rw [fraction_eq]
  simp

@[simp] theorem fraction_univ (e : Fin d ↪ Fin m) : fraction e Finset.univ = 1 := by
  classical
  rw [fraction_eq,Finset.card_univ,card_tuples]
  exact div_self (by exact_mod_cast (tuple_count_pos e).ne')

/-- Each individual ordered distinct tuple has exactly the same atom mass. -/
theorem fraction_singleton (e a : Fin d ↪ Fin m) :
    fraction e {a} = 1 / (m.descFactorial d : ℚ) := by
  classical
  rw [fraction_eq,Finset.card_singleton,Nat.cast_one]

/-- In particular there is exactly one empty tuple even on an empty ground set. -/
theorem fraction_empty_ground :
    fraction (Function.Embedding.refl (Fin 0)) {Function.Embedding.refl (Fin 0)} = 1 := by
  rw [fraction_singleton]
  norm_num

#print axioms exists_permutation_between
#print axioms card_fiber_eq
#print axioms card_event
#print axioms card_event_mul_tuple_card
#print axioms fraction_eq
#print axioms real_fraction_eq
#print axioms fraction_empty_ground
end MaxCaterpillar.Frontier.RandomRestriction.UniformTuples
