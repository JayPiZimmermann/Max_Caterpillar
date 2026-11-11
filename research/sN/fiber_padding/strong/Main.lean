import research.sN.fiber_padding.strong.Max465Strong
import research.sN.fiber_padding.strong.Expansion
import research.sN.fiber_padding.strong.Counter2

/-! # Is the notion of padding strong enough?  Headline statements

Each headline of `research/sN/fiber_padding/strong/` is restated here as
`example : <full type> := <name>` and its axioms are printed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Padding.Strong.Main

open BigOperators MaxCaterpillar.Fiber.Padding MaxCaterpillar.Fiber.Padding.Strong

/-! ## Definitions unfold as documented -/

example {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) (j : Fin h₁) (x : Point N) :
    act₁ net j x = relu ((∑ i, net.W₁ j i * x i) + net.b₁ j) := rfl

example {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) (k : Fin h₂) (x : Point N) :
    pre₂ net k x =
      (∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k := rfl

example {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) (x : Point N) :
    net.eval x = (∑ k, net.w₃ k * act₂ net k x) + net.b₃ := rfl

example {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) :
    HasMergeableOrRedundantNeuron net ↔
      (HasRemovableNeuron net ∨
        (∃ j', ∃ (c : Fin h₁ → ℝ) (c₀ : ℝ), c j' = 0 ∧
          ∀ x, act₁ net j' x = (∑ j, c j * act₁ net j x) + c₀) ∨
        (∃ k', ∃ (c : Fin h₂ → ℝ) (c₀ : ℝ), c k' = 0 ∧
          ∀ x, act₂ net k' x = (∑ k, c k * act₂ net k x) + c₀) ∨
        ∃ k k', k ≠ k' ∧ (∀ x, 0 ≤ pre₂ net k x) ∧ (∀ x, 0 ≤ pre₂ net k' x) ∧
          ∃ s M : ℝ, net.w₃ k' = s * net.w₃ k ∧
            ∀ x, 0 ≤ pre₂ net k x + s * pre₂ net k' x + M) := Iff.rfl

example {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) :
    HasListedDegeneracy net ↔
      (HasRemovableNeuron net ∨
        (∃ j j', j ≠ j' ∧ ∃ c : ℝ, 0 ≤ c ∧ (∀ i, net.W₁ j' i = c * net.W₁ j i) ∧
          net.b₁ j' = c * net.b₁ j) ∨
        (∃ k k', k ≠ k' ∧ ∃ c : ℝ, 0 ≤ c ∧ (∀ j, net.W₂ k' j = c * net.W₂ k j) ∧
          net.b₂ k' = c * net.b₂ k) ∨
        (∃ j, ∀ x : Point N, (∑ i, net.W₁ j i * x i) + net.b₁ j ≤ 0) ∨
        (∃ k, ∀ x : Point N, pre₂ net k x ≤ 0) ∨
        (∃ j, ∀ i, net.W₁ j i = 0) ∨
        (∃ k, ∃ c₀ : ℝ, ∀ x : Point N, pre₂ net k x = c₀) ∨
        ∃ k k', k ≠ k' ∧ (∀ x, 0 ≤ pre₂ net k x) ∧ (∀ x, 0 ≤ pre₂ net k' x) ∧
          0 ≤ net.w₃ k * net.w₃ k') := Iff.rfl

/-! ## General `N h₁ h₂`: the user's conjecture -/

example {N h₁ h₂ : ℕ} {net : Network N h₁ h₂} (h : HasListedDegeneracy net) :
    HasMergeableOrRedundantNeuron net := h.hasMergeableOrRedundantNeuron

example {N h₁ h₂ : ℕ} [NeZero N] (net : ExactFiber N h₁ h₂)
    (h : HasMergeableOrRedundantNeuron net.val) :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧ HasZeroNeuron net'.val :=
  exists_joined_hasZeroNeuron_of_mergeableOrRedundant net h

example {N h₁ h₂ : ℕ} [NeZero N] (net : ExactFiber N h₁ h₂)
    (h : HasListedDegeneracy net.val) :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧ HasZeroNeuron net'.val :=
  exists_joined_hasZeroNeuron_of_listedDegeneracy net h

example {N h₁ h₂ : ℕ} [NeZero N] (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂,
      HasMergeableOrRedundantNeuron net.val ∧
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C :=
  isReducibleComponent_iff_mergeableOrRedundant C

example {N h₁ h₂ : ℕ} [NeZero N] (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasListedDegeneracy net.val ∧
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C :=
  isReducibleComponent_iff_listedDegeneracy C

example {N h₁ h₂ : ℕ} [NeZero N] (C : ConnectedComponents (ExactFiber N h₁ h₂)) :
    IsReducibleRawComponent C ↔ ∃ net : ExactFiber N h₁ h₂,
      HasMergeableOrRedundantNeuron net.val ∧
      (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C :=
  isReducibleRawComponent_iff_mergeableOrRedundant C

example {N h₁ h₂ : ℕ} [NeZero N] (C : ConnectedComponents (ExactFiber N h₁ h₂)) :
    IsReducibleRawComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasListedDegeneracy net.val ∧
      (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C :=
  isReducibleRawComponent_iff_listedDegeneracy C

/-! ## General `N h₁ h₂`: the intrinsic formulation -/

example {N h₁ h₂ H₁ H₂ : ℕ} {big : Network N H₁ H₂} {small : Network N h₁ h₂}
    {φ₁ : Fin H₁ → Option (Fin h₁)} {φ₂ : Fin H₂ → Option (Fin h₂)}
    (h : IsExpansionOf big small φ₁ φ₂) (x : Point N) : big.eval x = small.eval x :=
  h.eval_eq x

example {N h₁ h₂ H₁ H₂ : ℕ} {big : Network N H₁ H₂} {small : Network N h₁ h₂}
    {e₁ : Fin h₁ ↪ Fin H₁} {e₂ : Fin h₂ ↪ Fin H₂} (h : IsPaddingOf big small e₁ e₂) :
    IsExpansionOf big small (Function.partialInv e₁) (Function.partialInv e₂) :=
  h.isExpansionOf

example {N H₁ H₂ : ℕ} [NeZero N] {big : Network N H₁ H₂} (h : IsExpandedSolution big) :
    (∀ x, big.eval x = Maximum N x) ∧ HasMergeableOrRedundantNeuron big :=
  ⟨h.exact, h.hasMergeableOrRedundantNeuron⟩

example {N h₁ h₂ : ℕ} [NeZero N] (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, IsExpandedSolution net.val ∧
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C :=
  isReducibleComponent_iff_expanded C

example {N h₁ h₂ : ℕ} [NeZero N] (C : ConnectedComponents (ExactFiber N h₁ h₂)) :
    IsReducibleRawComponent C ↔ ∃ net : ExactFiber N h₁ h₂, IsExpandedSolution net.val ∧
      (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C :=
  isReducibleRawComponent_iff_expanded C

/-! ## Max4 at widths (6,5) and (6,3) -/

example (net : ExactFiber 4 6 5)
    (hC : ((quotientMk net : SymmetryQuotient 4 6 5) :
      ConnectedComponents (SymmetryQuotient 4 6 5)) ≠ pairedComponent) :
    ¬ HasMergeableOrRedundantNeuron net.val :=
  not_mergeableOrRedundant_of_component_ne net hC

example (net : ExactFiber 4 6 5)
    (hC : ((quotientMk net : SymmetryQuotient 4 6 5) :
      ConnectedComponents (SymmetryQuotient 4 6 5)) ≠ pairedComponent) :
    ¬ HasListedDegeneracy net.val :=
  not_listedDegeneracy_of_component_ne net hC

/-- In a non-paired (6,5) component no network is an expansion of a smaller exact network. -/
theorem not_expandedSolution_of_component_ne (net : ExactFiber 4 6 5)
    (hC : ((quotientMk net : SymmetryQuotient 4 6 5) :
      ConnectedComponents (SymmetryQuotient 4 6 5)) ≠ pairedComponent) :
    ¬ IsExpandedSolution net.val := fun h =>
  not_mergeableOrRedundant_of_component_ne net hC h.hasMergeableOrRedundantNeuron

/-- In a non-paired (6,5) component no network can be deformed inside the exact fiber to a
network with a removable neuron (this excludes every reduction that is realized by a path). -/
theorem not_removable_of_joined_of_component_ne (net net' : ExactFiber 4 6 5)
    (hC : ((quotientMk net : SymmetryQuotient 4 6 5) :
      ConnectedComponents (SymmetryQuotient 4 6 5)) ≠ pairedComponent)
    (hj : Joined net net') : ¬ HasRemovableNeuron net'.val := fun hrem =>
  hC ((quotient_component_eq_of_joined hj).trans
    ((isReducibleComponent_iff_eq_pairedComponent _).mp ⟨net', hrem, rfl⟩))

example :
    ∃ C₀ : ConnectedComponents (SymmetryQuotient 4 6 5),
      ∀ C : ConnectedComponents (SymmetryQuotient 4 6 5),
        (∃ net : ExactFiber 4 6 5, HasMergeableOrRedundantNeuron net.val ∧
          ((quotientMk net : SymmetryQuotient 4 6 5) :
            ConnectedComponents (SymmetryQuotient 4 6 5)) = C) ↔ C = C₀ :=
  max4_6_5_exactly_one_component_with_mergeableOrRedundant

example :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∃ net : ExactFiber 4 6 5, HasMergeableOrRedundantNeuron net.val ∧
        ((quotientMk net : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C} = 1 :=
  max4_6_5_mergeableOrRedundant_component_count

example :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∀ net : ExactFiber 4 6 5,
        ((quotientMk net : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C →
        ¬ HasMergeableOrRedundantNeuron net.val} = 64 :=
  max4_6_5_exactly_64_components_without_mergeableOrRedundant

example :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∃ net : ExactFiber 4 6 5, HasListedDegeneracy net.val ∧
        ((quotientMk net : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C} = 1 :=
  max4_6_5_listedDegeneracy_component_count

example :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∀ net : ExactFiber 4 6 5,
        ((quotientMk net : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C →
        ¬ HasListedDegeneracy net.val} = 64 :=
  max4_6_5_exactly_64_components_without_listedDegeneracy

/-- Count with the intrinsic notion: exactly 64 components contain no expansion of a smaller
exact network. -/
theorem max4_6_5_exactly_64_components_without_expandedSolution :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∀ net : ExactFiber 4 6 5,
        ((quotientMk net : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C →
        ¬ IsExpandedSolution net.val} = 64 := by
  rw [← max4_6_5_irreducible_component_count]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ?_)
  rw [isReducibleComponent_iff_expanded]
  constructor
  · rintro h ⟨net, hd, hC⟩
    exact h net hC hd
  · intro h net hC hd
    exact h ⟨net, hd, hC⟩

example :
    ∃ C : ConnectedComponents (ExactFiber 4 6 5), ∀ net : ExactFiber 4 6 5,
      (net : ConnectedComponents (ExactFiber 4 6 5)) = C →
        ¬ HasMergeableOrRedundantNeuron net.val :=
  max4_6_5_exists_raw_component_without_mergeableOrRedundant

example (net : Network 4 6 3) (hnet : ∀ x, net.eval x = Maximum 4 x) :
    ¬ HasMergeableOrRedundantNeuron net :=
  max4_6_3_no_mergeableOrRedundant net hnet

/-! ## Counterexamples: what is NOT a degeneracy -/

example :
    ∃ net : ExactFiber 4 6 3,
      (∃ j j', j ≠ j' ∧ (∀ i, net.val.W₁ j' i = -net.val.W₁ j i) ∧
        net.val.b₁ j' = -net.val.b₁ j ∧ ∀ k, net.val.W₂ k j' = -net.val.W₂ k j) ∧
      (∃ k k', k ≠ k' ∧ (∀ j, net.val.W₂ k' j = -net.val.W₂ k j) ∧
        net.val.b₂ k' = -net.val.b₂ k ∧ net.val.w₃ k' = -net.val.w₃ k) ∧
      ¬ HasMergeableOrRedundantNeuron net.val ∧
      ¬ IsReducibleComponent ((quotientMk net : SymmetryQuotient 4 6 3) :
        ConnectedComponents (SymmetryQuotient 4 6 3)) :=
  oppositePair_not_reducible

example :
    ∃ net : ExactFiber 2 3 2,
      (∃ k k' : Fin 2, k ≠ k' ∧ (∀ x, 0 ≤ pre₂ net.val k x) ∧ (∀ x, 0 ≤ pre₂ net.val k' x) ∧
        net.val.w₃ k * net.val.w₃ k' < 0) ∧
      ¬ HasMergeableOrRedundantNeuron net.val ∧
      ¬ IsReducibleComponent ((quotientMk net : SymmetryQuotient 2 3 2) :
        ConnectedComponents (SymmetryQuotient 2 3 2)) :=
  active_opposite_sign_not_reducible

#print axioms exists_joined_hasZeroNeuron_of_mergeableOrRedundant
#print axioms exists_joined_hasZeroNeuron_of_listedDegeneracy
#print axioms isReducibleComponent_iff_mergeableOrRedundant
#print axioms isReducibleComponent_iff_listedDegeneracy
#print axioms isReducibleRawComponent_iff_mergeableOrRedundant
#print axioms isReducibleRawComponent_iff_listedDegeneracy
#print axioms IsExpansionOf.eval_eq
#print axioms MaxCaterpillar.Fiber.Padding.IsPaddingOf.isExpansionOf
#print axioms isExpansionOf_duplicateFirst
#print axioms IsExpandedSolution.hasMergeableOrRedundantNeuron
#print axioms isReducibleComponent_iff_expanded
#print axioms isReducibleRawComponent_iff_expanded
#print axioms not_mergeableOrRedundant_of_component_ne
#print axioms not_listedDegeneracy_of_component_ne
#print axioms no_degeneracy_unfolded_of_component_ne
#print axioms not_expandedSolution_of_component_ne
#print axioms not_removable_of_joined_of_component_ne
#print axioms max4_6_5_exactly_one_component_with_mergeableOrRedundant
#print axioms max4_6_5_mergeableOrRedundant_component_count
#print axioms max4_6_5_exactly_64_components_without_mergeableOrRedundant
#print axioms max4_6_5_listedDegeneracy_component_count
#print axioms max4_6_5_exactly_64_components_without_listedDegeneracy
#print axioms max4_6_5_exactly_64_components_without_expandedSolution
#print axioms max4_6_5_exists_raw_component_without_mergeableOrRedundant
#print axioms max4_6_3_no_mergeableOrRedundant
#print axioms oppositePair_not_reducible
#print axioms active_opposite_sign_not_reducible

end MaxCaterpillar.Fiber.Padding.Strong.Main
