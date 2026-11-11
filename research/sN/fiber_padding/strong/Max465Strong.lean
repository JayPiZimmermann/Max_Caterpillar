import research.sN.fiber_padding.strong.Strong
import research.sN.fiber_padding.Max465
import research.sN.fiber_padding.Max4General

/-! # The Max4 corollaries under the strong notion

* At widths (6,5): in the 64 components different from `pairedComponent` no network has a
  mergeable, dead, constant or otherwise redundant hidden neuron; the count theorems restated
  with `HasMergeableOrRedundantNeuron` and with the weight-level list `HasListedDegeneracy`.
* At the minimal widths (6,3): no exact network has any such degeneracy.
* Counterexample to the remaining item of (e): the minimal network `maxFourNet` has two
  first-hidden-layer neurons with opposite incoming rows and opposite outgoing columns (and
  two second-hidden-layer neurons with opposite incoming rows and opposite output weights),
  but its component is not reducible.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Padding.Strong

open BigOperators MaxCaterpillar.Fiber.Padding

/-! ## General principle -/

/-- If no exact network of an architecture has a removable hidden neuron, then no exact
network of that architecture has a mergeable or redundant hidden neuron. -/
theorem not_mergeableOrRedundant_of_no_removable {N h₁ h₂ : ℕ} [NeZero N]
    (hno : ∀ net : ExactFiber N h₁ h₂, ¬ HasRemovableNeuron net.val)
    (net : ExactFiber N h₁ h₂) : ¬ HasMergeableOrRedundantNeuron net.val := by
  intro h
  obtain ⟨net', -, hrem⟩ := exists_joined_hasRemovableNeuron net h
  exact hno net' hrem

/-! ## Widths (6,5) -/

/-- A component of the (6,5) quotient contains a network with a mergeable or redundant
hidden neuron iff it is the paired component. -/
theorem mergeableOrRedundant_component_iff_eq_pairedComponent
    (C : ConnectedComponents (SymmetryQuotient 4 6 5)) :
    (∃ net : ExactFiber 4 6 5, HasMergeableOrRedundantNeuron net.val ∧
      ((quotientMk net : SymmetryQuotient 4 6 5) :
        ConnectedComponents (SymmetryQuotient 4 6 5)) = C) ↔ C = pairedComponent := by
  rw [← isReducibleComponent_iff_mergeableOrRedundant,
    isReducibleComponent_iff_eq_pairedComponent]

theorem listedDegeneracy_component_iff_eq_pairedComponent
    (C : ConnectedComponents (SymmetryQuotient 4 6 5)) :
    (∃ net : ExactFiber 4 6 5, HasListedDegeneracy net.val ∧
      ((quotientMk net : SymmetryQuotient 4 6 5) :
        ConnectedComponents (SymmetryQuotient 4 6 5)) = C) ↔ C = pairedComponent := by
  rw [← isReducibleComponent_iff_listedDegeneracy,
    isReducibleComponent_iff_eq_pairedComponent]

/-- In each component other than the paired one, NO exact network has a mergeable or
redundant hidden neuron. -/
theorem not_mergeableOrRedundant_of_component_ne (net : ExactFiber 4 6 5)
    (hC : ((quotientMk net : SymmetryQuotient 4 6 5) :
      ConnectedComponents (SymmetryQuotient 4 6 5)) ≠ pairedComponent) :
    ¬ HasMergeableOrRedundantNeuron net.val := fun h =>
  hC ((mergeableOrRedundant_component_iff_eq_pairedComponent _).mp ⟨net, h, rfl⟩)

theorem not_listedDegeneracy_of_component_ne (net : ExactFiber 4 6 5)
    (hC : ((quotientMk net : SymmetryQuotient 4 6 5) :
      ConnectedComponents (SymmetryQuotient 4 6 5)) ≠ pairedComponent) :
    ¬ HasListedDegeneracy net.val := fun h =>
  not_mergeableOrRedundant_of_component_ne net hC h.hasMergeableOrRedundantNeuron

/-- The previous theorem with every definition unfolded to weights, biases and the functions
computed inside the network. In a non-paired (6,5) component, for every exact network:
1. no two first-hidden-layer neurons have nonnegatively proportional (row, bias);
2. no two second-hidden-layer neurons have nonnegatively proportional (row, bias);
3. no first-hidden-layer neuron is inactive at every input;
4. no second-hidden-layer neuron is inactive at every input;
5. no first-hidden-layer neuron has zero incoming weights (for any bias);
6. no second-hidden-layer neuron has a constant preactivation;
7. no two second-hidden-layer neurons are both active at every input with output weights
   of non-opposite signs;
8. no first-hidden-layer neuron has zero outgoing weights and no output weight vanishes. -/
theorem no_degeneracy_unfolded_of_component_ne (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hC : ((quotientMk ⟨net, hnet⟩ : SymmetryQuotient 4 6 5) :
      ConnectedComponents (SymmetryQuotient 4 6 5)) ≠ pairedComponent) :
    (∀ j j' : Fin 6, j ≠ j' → ∀ c : ℝ, 0 ≤ c →
      ¬ ((∀ i, net.W₁ j' i = c * net.W₁ j i) ∧ net.b₁ j' = c * net.b₁ j)) ∧
    (∀ k k' : Fin 5, k ≠ k' → ∀ c : ℝ, 0 ≤ c →
      ¬ ((∀ j, net.W₂ k' j = c * net.W₂ k j) ∧ net.b₂ k' = c * net.b₂ k)) ∧
    (∀ j : Fin 6, ∃ x : Point 4, 0 < (∑ i, net.W₁ j i * x i) + net.b₁ j) ∧
    (∀ k : Fin 5, ∃ x : Point 4,
      0 < (∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k) ∧
    (∀ j : Fin 6, ∃ i, net.W₁ j i ≠ 0) ∧
    (∀ k : Fin 5, ∀ c₀ : ℝ, ∃ x : Point 4,
      (∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k ≠ c₀) ∧
    (∀ k k' : Fin 5, k ≠ k' → 0 ≤ net.w₃ k * net.w₃ k' →
      ∃ x : Point 4,
        (∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k < 0 ∨
        (∑ j, net.W₂ k' j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k' < 0) ∧
    (∀ j : Fin 6, ∃ k, net.W₂ k j ≠ 0) ∧ (∀ k : Fin 5, net.w₃ k ≠ 0) := by
  have hno : ¬ HasListedDegeneracy net :=
    not_listedDegeneracy_of_component_ne ⟨net, hnet⟩ hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j j' hne c hc h
    exact hno (Or.inr (Or.inl ⟨j, j', hne, c, hc, h.1, h.2⟩))
  · intro k k' hne c hc h
    exact hno (Or.inr (Or.inr (Or.inl ⟨k, k', hne, c, hc, h.1, h.2⟩)))
  · intro j
    by_contra h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, fun x => not_lt.mp fun hx => h ⟨x, hx⟩⟩))))
  · intro k
    by_contra h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, fun x => not_lt.mp fun hx => h ⟨x, hx⟩⟩)))))
  · intro j
    by_contra h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨j, fun i => not_not.mp fun hi => h ⟨i, hi⟩⟩))))))
  · intro k c₀
    by_contra h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, c₀, fun x => not_not.mp fun hx => h ⟨x, hx⟩⟩)))))))
  · intro k k' hne hw
    by_contra h
    refine hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨k, k', hne, fun x => ?_, fun x => ?_, hw⟩)))))))
    · exact not_lt.mp fun hx => h ⟨x, Or.inl hx⟩
    · exact not_lt.mp fun hx => h ⟨x, Or.inr hx⟩
  · intro j
    by_contra h
    exact hno (Or.inl (Or.inl ⟨j, Or.inl fun k => not_not.mp fun hk => h ⟨k, hk⟩⟩))
  · intro k hk
    exact hno (Or.inl (Or.inr ⟨k, Or.inl hk⟩))

/-- Exactly one of the components of the (6,5) quotient contains a network with a
mergeable or redundant hidden neuron. -/
theorem max4_6_5_exactly_one_component_with_mergeableOrRedundant :
    ∃ C₀ : ConnectedComponents (SymmetryQuotient 4 6 5),
      ∀ C : ConnectedComponents (SymmetryQuotient 4 6 5),
        (∃ net : ExactFiber 4 6 5, HasMergeableOrRedundantNeuron net.val ∧
          ((quotientMk net : SymmetryQuotient 4 6 5) :
            ConnectedComponents (SymmetryQuotient 4 6 5)) = C) ↔ C = C₀ :=
  ⟨pairedComponent, mergeableOrRedundant_component_iff_eq_pairedComponent⟩

theorem max4_6_5_mergeableOrRedundant_component_count :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∃ net : ExactFiber 4 6 5, HasMergeableOrRedundantNeuron net.val ∧
        ((quotientMk net : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C} = 1 := by
  rw [← max4_6_5_reducible_component_count]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun C =>
    (isReducibleComponent_iff_mergeableOrRedundant C).symm)

/-- Exactly 64 components of the (6,5) quotient contain no network with a mergeable or
redundant hidden neuron. -/
theorem max4_6_5_exactly_64_components_without_mergeableOrRedundant :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∀ net : ExactFiber 4 6 5,
        ((quotientMk net : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C →
        ¬ HasMergeableOrRedundantNeuron net.val} = 64 := by
  rw [← max4_6_5_irreducible_component_count]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ?_)
  rw [isReducibleComponent_iff_mergeableOrRedundant]
  constructor
  · rintro h ⟨net, hd, hC⟩
    exact h net hC hd
  · intro h net hC hd
    exact h ⟨net, hd, hC⟩

theorem max4_6_5_listedDegeneracy_component_count :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∃ net : ExactFiber 4 6 5, HasListedDegeneracy net.val ∧
        ((quotientMk net : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C} = 1 := by
  rw [← max4_6_5_reducible_component_count]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun C =>
    (isReducibleComponent_iff_listedDegeneracy C).symm)

theorem max4_6_5_exactly_64_components_without_listedDegeneracy :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∀ net : ExactFiber 4 6 5,
        ((quotientMk net : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C →
        ¬ HasListedDegeneracy net.val} = 64 := by
  rw [← max4_6_5_irreducible_component_count]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ?_)
  rw [isReducibleComponent_iff_listedDegeneracy]
  constructor
  · rintro h ⟨net, hd, hC⟩
    exact h net hC hd
  · intro h net hC hd
    exact h ⟨net, hd, hC⟩

/-- Raw fiber: some component of the exact (6,5) fiber (before the symmetry quotient)
contains no network with a mergeable or redundant hidden neuron. -/
theorem max4_6_5_exists_raw_component_without_mergeableOrRedundant :
    ∃ C : ConnectedComponents (ExactFiber 4 6 5), ∀ net : ExactFiber 4 6 5,
      (net : ConnectedComponents (ExactFiber 4 6 5)) = C →
        ¬ HasMergeableOrRedundantNeuron net.val := by
  by_contra h
  apply max4_6_5_not_every_raw_component_reducible
  intro C
  rw [isReducibleRawComponent_iff_mergeableOrRedundant]
  by_contra hC
  exact h ⟨C, fun net hnet hd => hC ⟨net, hd, hnet⟩⟩

/-! ## Minimal widths (6,3) -/

/-- At the minimal widths (6,3) no exact Max4 network has a mergeable or redundant hidden
neuron. -/
theorem max4_6_3_no_mergeableOrRedundant (net : Network 4 6 3)
    (hnet : ∀ x, net.eval x = Maximum 4 x) : ¬ HasMergeableOrRedundantNeuron net :=
  not_mergeableOrRedundant_of_no_removable
    (fun n => max4_6_3_no_removable n.val n.property) ⟨net, hnet⟩

/-! ## A pair of opposite neurons is NOT a degeneracy -/

/-- Two first-hidden-layer neurons with opposite incoming rows and biases whose outgoing
columns are opposite (together they feed the linear function `W₁ j · x + b₁ j` into the
second hidden layer). -/
def FirstOppositePair {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) (j j' : Fin h₁) : Prop :=
  j ≠ j' ∧ (∀ i, net.W₁ j' i = -net.W₁ j i) ∧ net.b₁ j' = -net.b₁ j ∧
    ∀ k, net.W₂ k j' = -net.W₂ k j

/-- Two second-hidden-layer neurons with opposite incoming rows and biases and opposite
output weights. -/
def SecondOppositePair {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) (k k' : Fin h₂) : Prop :=
  k ≠ k' ∧ (∀ j, net.W₂ k' j = -net.W₂ k j) ∧ net.b₂ k' = -net.b₂ k ∧
    net.w₃ k' = -net.w₃ k

theorem maxFourNet_firstOppositePair : FirstOppositePair Frontier.maxFourNet 2 3 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · have h3 : Frontier.maxFourNet.W₁ 3 = ![0, -1, 0, 0] := rfl
    have h2 : Frontier.maxFourNet.W₁ 2 = ![0, 1, 0, 0] := rfl
    intro i
    rw [h3, h2]
    fin_cases i <;> simp
  · simp [Frontier.maxFourNet]
  · have c3 : ∀ k, Frontier.maxFourNet.W₂ k 3 = (![0, 0, -1] : Fin 3 → ℝ) k := by
      intro k
      fin_cases k <;> rfl
    have c2 : ∀ k, Frontier.maxFourNet.W₂ k 2 = (![0, 0, 1] : Fin 3 → ℝ) k := by
      intro k
      fin_cases k <;> rfl
    intro k
    rw [c3, c2]
    fin_cases k <;> simp

theorem maxFourNet_secondOppositePair : SecondOppositePair Frontier.maxFourNet 0 1 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp [Frontier.maxFourNet]
  · simp [Frontier.maxFourNet]
  · simp [Frontier.maxFourNet]

/-- **Counterexample.** There is an exact network (the minimal Max4 network of widths (6,3))
with a pair of opposite first-hidden-layer neurons with opposite outgoing columns and a pair
of opposite second-hidden-layer neurons with opposite output weights, whose component is
not reducible, and which has no mergeable or redundant neuron. So "negatively proportional
rows with opposite outgoing weights" is not a reduction. -/
theorem oppositePair_not_reducible :
    ∃ net : ExactFiber 4 6 3,
      (∃ j j', FirstOppositePair net.val j j') ∧ (∃ k k', SecondOppositePair net.val k k') ∧
      ¬ HasMergeableOrRedundantNeuron net.val ∧
      ¬ IsReducibleComponent ((quotientMk net : SymmetryQuotient 4 6 3) :
        ConnectedComponents (SymmetryQuotient 4 6 3)) :=
  ⟨⟨Frontier.maxFourNet, Frontier.maxFourNet_eval⟩, ⟨2, 3, maxFourNet_firstOppositePair⟩,
    ⟨0, 1, maxFourNet_secondOppositePair⟩,
    max4_6_3_no_mergeableOrRedundant _ Frontier.maxFourNet_eval,
    max4_6_3_no_reducible_component _⟩

#print axioms not_mergeableOrRedundant_of_component_ne
#print axioms no_degeneracy_unfolded_of_component_ne
#print axioms max4_6_5_exactly_one_component_with_mergeableOrRedundant
#print axioms max4_6_5_mergeableOrRedundant_component_count
#print axioms max4_6_5_exactly_64_components_without_mergeableOrRedundant
#print axioms max4_6_5_listedDegeneracy_component_count
#print axioms max4_6_5_exactly_64_components_without_listedDegeneracy
#print axioms max4_6_5_exists_raw_component_without_mergeableOrRedundant
#print axioms max4_6_3_no_mergeableOrRedundant
#print axioms oppositePair_not_reducible

end MaxCaterpillar.Fiber.Padding.Strong
