import MaxCaterpillar.Frontier.RandomRestriction.SelectedSetProbability

/-! # Four fixed vertices in the first five permutation positions

These are the d=4 specializations of the actual finite-permutation law.
The public events retain literal label-to-position predicates.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
variable {N : ℕ}

noncomputable def selectedFive (τ : Equiv.Perm (Fin N)) : Finset (Fin N) :=
  SelectedSetProbability.selectedLabels τ

@[simp] theorem mem_selectedFive (τ : Equiv.Perm (Fin N)) (v : Fin N) :
    v ∈ selectedFive τ ↔ (τ v).val < 5 := GoodEvent.mem_smallRankGaps τ v

theorem selectedFive_card (hN : 5 ≤ N) (τ : Equiv.Perm (Fin N)) :
    (selectedFive τ).card = 5 := SelectedSetProbability.selectedLabels_card hN τ

noncomputable def selectedFourTuples (N : ℕ) : Finset (Fin 4 ↪ Fin N) :=
  SelectedSetProbability.selectedTuples N 4

@[simp] theorem mem_selectedFourTuples (a : Fin 4 ↪ Fin N) :
    a ∈ selectedFourTuples N ↔ ∀ i, (a i).val < 5 :=
  SelectedSetProbability.mem_selectedTuples a

/-- The five-prefix restriction equivalence is supplied by the generic law. -/
def selectedFourTupleEquiv (hN : 5 ≤ N) :
    (Fin 4 ↪ Fin 5) ≃ {a : Fin 4 ↪ Fin N // a ∈ selectedFourTuples N} :=
  SelectedSetProbability.selectedTupleEquiv hN

theorem selectedFourTuples_card_descFactorial (hN : 5 ≤ N) :
    (selectedFourTuples N).card = Nat.descFactorial 5 4 :=
  SelectedSetProbability.selectedTuples_card hN

theorem selectedFourTuples_card (hN : 5 ≤ N) :
    (selectedFourTuples N).card = 120 :=
  (selectedFourTuples_card_descFactorial hN).trans (by decide)

/-- Literal event: all four fixed vertex labels receive positions below 5. -/
noncomputable def selectedFourEvent (e : Fin 4 ↪ Fin N) :
    Finset (Equiv.Perm (Fin N)) := by
  classical
  exact Finset.univ.filter fun τ => ∀ i, (τ (e i)).val < 5

@[simp] theorem mem_selectedFourEvent (e : Fin 4 ↪ Fin N)
    (τ : Equiv.Perm (Fin N)) :
    τ ∈ selectedFourEvent e ↔ ∀ i, (τ (e i)).val < 5 := by
  classical
  simp [selectedFourEvent]

theorem selectedFourEvent_eq_uniformTuples (e : Fin 4 ↪ Fin N) :
    selectedFourEvent e = UniformTuples.event e (selectedFourTuples N) :=
  SelectedSetProbability.tupleEvent_eq_uniformTuples e

/-- Exact natural-number count, before division by permutation-space size. -/
theorem selectedFourEvent_card_mul (hN : 5 ≤ N) (e : Fin 4 ↪ Fin N) :
    (selectedFourEvent e).card * N.descFactorial 4 =
      120 * Fintype.card (Equiv.Perm (Fin N)) := by
  simpa only [show Nat.descFactorial 5 4 = 120 by decide] using
    SelectedSetProbability.tupleEvent_card_mul hN e

/-- The actual uniform-permutation probability is exactly 120/(N)_4. -/
theorem selectedFourEvent_fraction (hN : 5 ≤ N) (e : Fin 4 ↪ Fin N) :
    ((selectedFourEvent e).card : ℝ) /
        (Fintype.card (Equiv.Perm (Fin N)) : ℝ) =
      120 / (N.descFactorial 4 : ℝ) := by
  simpa only [show Nat.descFactorial 5 4 = 120 by decide] using
    SelectedSetProbability.tupleEvent_fraction hN e

/-- The same literal event for a fixed vertex set, without choosing an order. -/
noncomputable def selectedFourSetEvent (T : Finset (Fin N)) :
    Finset (Equiv.Perm (Fin N)) := by
  classical
  exact Finset.univ.filter fun τ => ∀ v ∈ T, (τ v).val < 5

@[simp] theorem mem_selectedFourSetEvent (T : Finset (Fin N))
    (τ : Equiv.Perm (Fin N)) :
    τ ∈ selectedFourSetEvent T ↔ ∀ v ∈ T, (τ v).val < 5 := by
  classical
  simp [selectedFourSetEvent]

theorem mem_selectedFourSetEvent_iff_subset (T : Finset (Fin N))
    (τ : Equiv.Perm (Fin N)) :
    τ ∈ selectedFourSetEvent T ↔ T ⊆ selectedFive τ := by
  rw [mem_selectedFourSetEvent]
  constructor
  · intro h v hv
    exact (mem_selectedFive τ v).mpr (h v hv)
  · intro h v hv
    exact (mem_selectedFive τ v).mp (h hv)

theorem selectedFourSetEvent_eq_containsEvent (T : Finset (Fin N)) :
    selectedFourSetEvent T = SelectedSetProbability.containsEvent T := by
  ext τ
  rw [mem_selectedFourSetEvent_iff_subset,SelectedSetProbability.mem_containsEvent]
  rfl

theorem selectedFourSetEvent_card_mul (hN : 5 ≤ N)
    (T : Finset (Fin N)) (hT : T.card = 4) :
    (selectedFourSetEvent T).card * N.descFactorial 4 =
      120 * Fintype.card (Equiv.Perm (Fin N)) := by
  rw [selectedFourSetEvent_eq_containsEvent]
  exact SelectedSetProbability.fourSet_containsEvent_card_mul hN T hT

theorem selectedFourSetEvent_fraction (hN : 5 ≤ N)
    (T : Finset (Fin N)) (hT : T.card = 4) :
    ((selectedFourSetEvent T).card : ℝ) /
        (Fintype.card (Equiv.Perm (Fin N)) : ℝ) =
      120 / (N.descFactorial 4 : ℝ) := by
  rw [selectedFourSetEvent_eq_containsEvent]
  exact SelectedSetProbability.fourSet_containsEvent_fraction hN T hT

#check @selectedFourEvent_fraction
#check @selectedFourSetEvent_fraction
#print axioms selectedFourTupleEquiv
#print axioms selectedFourEvent_card_mul
#print axioms selectedFourEvent_fraction
#print axioms selectedFourSetEvent_card_mul
#print axioms selectedFourSetEvent_fraction
end MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
