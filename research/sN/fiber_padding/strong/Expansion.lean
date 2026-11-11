import research.sN.fiber_padding.strong.Strong
import Mathlib.Data.Fintype.Card

/-! # The intrinsic formulation: expansions of smaller exact networks

`IsExpansionOf big small φ₁ φ₂` : every hidden neuron `J` of `big` is either a *copy* of a
hidden neuron of `small` (`φ J = some j`) or an *additional* neuron (`φ J = none`).

* a copy has the incoming row and bias of the original (for the second hidden layer: the
  incoming weights of a copy `K` of `k`, summed over all copies `J` of `j`, give `W₂ k j`);
* the outgoing weights of the copies of one neuron are *split*: they sum to the outgoing
  weight of the original;
* every additional neuron is removable (zero outgoing weights, or zero incoming weights and
  zero bias).

This contains zero padding along injections (`IsPaddingOf.isExpansionOf`), duplication of a
first-hidden-layer neuron with split outgoing weights (`isExpansionOf_duplicateFirst`), and
all their compositions in both layers.

`IsExpandedSolution big` : `big` is an expansion of an exact network of a strictly smaller
architecture.  Main theorems: an expansion computes the same function; an expanded solution
has a mergeable or redundant neuron; a component is reducible iff it contains an expanded
solution.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Padding.Strong

open BigOperators MaxCaterpillar.Fiber.Padding

variable {N h₁ h₂ : ℕ}

structure IsExpansionOf {H₁ H₂ : ℕ} (big : Network N H₁ H₂) (small : Network N h₁ h₂)
    (φ₁ : Fin H₁ → Option (Fin h₁)) (φ₂ : Fin H₂ → Option (Fin h₂)) : Prop where
  W₁ : ∀ J j, φ₁ J = some j → ∀ i, big.W₁ J i = small.W₁ j i
  b₁ : ∀ J j, φ₁ J = some j → big.b₁ J = small.b₁ j
  W₂ : ∀ K k, φ₂ K = some k → ∀ j,
    (∑ J, if φ₁ J = some j then big.W₂ K J else 0) = small.W₂ k j
  b₂ : ∀ K k, φ₂ K = some k → big.b₂ K = small.b₂ k
  w₃ : ∀ k, (∑ K, if φ₂ K = some k then big.w₃ K else 0) = small.w₃ k
  b₃ : big.b₃ = small.b₃
  extra₁ : ∀ J, φ₁ J = none → FirstRemovable big J
  extra₂ : ∀ K, φ₂ K = none → SecondRemovable big K

/-- Regrouping a sum along a partial map. -/
theorem sum_option_fiber {A B : ℕ} (φ : Fin A → Option (Fin B)) (w u : Fin A → ℝ)
    (v : Fin B → ℝ) (hsome : ∀ J j, φ J = some j → u J = v j)
    (hnone : ∀ J, φ J = none → w J * u J = 0) :
    (∑ J, w J * u J) = ∑ j, (∑ J, if φ J = some j then w J else 0) * v j := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rcases hJ : φ J with _ | j₀
  · rw [hnone J hJ]
    simp
  · rw [hsome J j₀ hJ]
    simp [ite_mul, Finset.sum_ite_eq]

section Eval

variable {H₁ H₂ : ℕ} {big : Network N H₁ H₂} {small : Network N h₁ h₂}
  {φ₁ : Fin H₁ → Option (Fin h₁)} {φ₂ : Fin H₂ → Option (Fin h₂)}

theorem IsExpansionOf.act₁_eq (h : IsExpansionOf big small φ₁ φ₂) {J : Fin H₁} {j : Fin h₁}
    (hJ : φ₁ J = some j) (x : Point N) : act₁ big J x = act₁ small j x := by
  unfold act₁
  rw [h.b₁ J j hJ]
  simp only [h.W₁ J j hJ]

theorem IsExpansionOf.pre₂_eq (h : IsExpansionOf big small φ₁ φ₂) {K : Fin H₂} {k : Fin h₂}
    (hK : φ₂ K = some k) (x : Point N) : pre₂ big K x = pre₂ small k x := by
  unfold pre₂
  rw [h.b₂ K k hK, sum_option_fiber φ₁ (fun J => big.W₂ K J) (fun J => act₁ big J x)
    (fun j => act₁ small j x) (fun J j hJ => h.act₁_eq hJ x) ?_]
  · simp only [h.W₂ K k hK]
  · intro J hJ
    show big.W₂ K J * act₁ big J x = 0
    rcases h.extra₁ J hJ with hd | hd
    · rw [hd K, zero_mul]
    · exact mul_eq_zero_of_right _ (hd.activation_eq_zero x)

theorem IsExpansionOf.act₂_eq (h : IsExpansionOf big small φ₁ φ₂) {K : Fin H₂} {k : Fin h₂}
    (hK : φ₂ K = some k) (x : Point N) : act₂ big K x = act₂ small k x := by
  unfold act₂
  rw [h.pre₂_eq hK x]

/-- An expansion computes the same function as the network it expands. -/
theorem IsExpansionOf.eval_eq (h : IsExpansionOf big small φ₁ φ₂) (x : Point N) :
    big.eval x = small.eval x := by
  rw [Strong.eval_eq, Strong.eval_eq, h.b₃,
    sum_option_fiber φ₂ big.w₃ (fun K => act₂ big K x) (fun k => act₂ small k x)
      (fun K k hK => h.act₂_eq hK x) ?_]
  · simp only [h.w₃]
  · intro K hK
    show big.w₃ K * act₂ big K x = 0
    rcases h.extra₂ K hK with hd | hd
    · rw [show big.w₃ K = 0 from hd, zero_mul]
    · exact mul_eq_zero_of_right _ (hd.activation_eq_zero x)

/-- If the first hidden layer of an expansion is strictly wider, the big network has a
removable first-hidden-layer neuron or two first-hidden-layer neurons with equal incoming
rows and biases. -/
theorem IsExpansionOf.first_degenerate (h : IsExpansionOf big small φ₁ φ₂) (hlt : h₁ < H₁) :
    (∃ J, FirstRemovable big J) ∨ ∃ J J', FirstProportional big J J' := by
  by_cases hnone : ∃ J, φ₁ J = none
  · obtain ⟨J, hJ⟩ := hnone
    exact Or.inl ⟨J, h.extra₁ J hJ⟩
  · have hsome : ∀ J, ∃ j, φ₁ J = some j := fun J =>
      Option.ne_none_iff_exists'.mp fun hJ => hnone ⟨J, hJ⟩
    choose f hf using hsome
    obtain ⟨J, J', hne, hJJ⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hlt)
    refine Or.inr ⟨J, J', hne, 1, zero_le_one, fun i => ?_, ?_⟩
    · rw [one_mul, h.W₁ J' (f J') (hf J'), h.W₁ J (f J) (hf J), hJJ]
    · rw [one_mul, h.b₁ J' (f J') (hf J'), h.b₁ J (f J) (hf J), hJJ]

/-- If the second hidden layer of an expansion is strictly wider, the big network has a
removable second-hidden-layer neuron or two second-hidden-layer neurons computing the same
function. -/
theorem IsExpansionOf.second_degenerate (h : IsExpansionOf big small φ₁ φ₂) (hlt : h₂ < H₂) :
    (∃ K, SecondRemovable big K) ∨ ∃ K, SecondDependent big K := by
  by_cases hnone : ∃ K, φ₂ K = none
  · obtain ⟨K, hK⟩ := hnone
    exact Or.inl ⟨K, h.extra₂ K hK⟩
  · have hsome : ∀ K, ∃ k, φ₂ K = some k := fun K =>
      Option.ne_none_iff_exists'.mp fun hK => hnone ⟨K, hK⟩
    choose f hf using hsome
    obtain ⟨K, K', hne, hKK⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hlt)
    refine Or.inr ⟨K', fun κ => if κ = K then 1 else 0, 0, if_neg (Ne.symm hne), fun x => ?_⟩
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      add_zero]
    rw [h.act₂_eq (hf K') x, h.act₂_eq (hf K) x, hKK]

theorem IsExpansionOf.hasMergeableOrRedundantNeuron (h : IsExpansionOf big small φ₁ φ₂)
    (hlt : h₁ < H₁ ∨ h₂ < H₂) : HasMergeableOrRedundantNeuron big := by
  rcases hlt with hlt | hlt
  · rcases h.first_degenerate hlt with ⟨J, hJ⟩ | ⟨J, J', hJ⟩
    · exact Or.inl (Or.inl ⟨J, hJ⟩)
    · exact Or.inr (Or.inl ⟨J', hJ.firstDependent⟩)
  · rcases h.second_degenerate hlt with ⟨K, hK⟩ | ⟨K, hK⟩
    · exact Or.inl (Or.inr ⟨K, hK⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨K, hK⟩))

/-- Zero padding along injections of the hidden neurons is an expansion. -/
theorem _root_.MaxCaterpillar.Fiber.Padding.IsPaddingOf.isExpansionOf
    {e₁ : Fin h₁ ↪ Fin H₁} {e₂ : Fin h₂ ↪ Fin H₂} (h : IsPaddingOf big small e₁ e₂) :
    IsExpansionOf big small (Function.partialInv e₁) (Function.partialInv e₂) := by
  have i₁ := Function.partialInv_of_injective e₁.injective
  have i₂ := Function.partialInv_of_injective e₂.injective
  refine ⟨?_, ?_, ?_, ?_, ?_, h.b₃, ?_, ?_⟩
  · intro J j hJ i
    rw [← (i₁ j J).mp hJ]
    exact h.W₁ j i
  · intro J j hJ
    rw [← (i₁ j J).mp hJ]
    exact h.b₁ j
  · intro K k hK j
    rw [← (i₂ k K).mp hK]
    simp only [i₁ j, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact h.W₂ k j
  · intro K k hK
    rw [← (i₂ k K).mp hK]
    exact h.b₂ k
  · intro k
    simp only [i₂ k, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact h.w₃ k
  · intro J hJ
    refine h.extra₁ J ?_
    rintro ⟨j, rfl⟩
    rw [Function.partialInv_left e₁.injective] at hJ
    exact Option.some_ne_none j hJ
  · intro K hK
    refine h.extra₂ K ?_
    rintro ⟨k, rfl⟩
    rw [Function.partialInv_left e₂.injective] at hK
    exact Option.some_ne_none k hK

end Eval

/-- Duplicating first-hidden-layer neuron `j₀` (the copy is the last neuron of `big`) with
split outgoing weights is an expansion. -/
theorem isExpansionOf_duplicateFirst (big : Network N (h₁ + 1) h₂) (small : Network N h₁ h₂)
    (j₀ : Fin h₁)
    (hW₁ : ∀ j i, big.W₁ (Fin.castSucc j) i = small.W₁ j i)
    (hb₁ : ∀ j, big.b₁ (Fin.castSucc j) = small.b₁ j)
    (hW₁' : ∀ i, big.W₁ (Fin.last h₁) i = small.W₁ j₀ i)
    (hb₁' : big.b₁ (Fin.last h₁) = small.b₁ j₀)
    (hW₂ : ∀ k j, j ≠ j₀ → big.W₂ k (Fin.castSucc j) = small.W₂ k j)
    (hsplit : ∀ k, big.W₂ k (Fin.castSucc j₀) + big.W₂ k (Fin.last h₁) = small.W₂ k j₀)
    (hb₂ : big.b₂ = small.b₂) (hw₃ : big.w₃ = small.w₃) (hb₃ : big.b₃ = small.b₃) :
    IsExpansionOf big small (Fin.lastCases (some j₀) (fun j => some j)) some := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hb₃, ?_, ?_⟩
  · intro J
    refine Fin.lastCases ?_ (fun j' => ?_) J
    · intro j hJ i
      rw [Fin.lastCases_last, Option.some.injEq] at hJ
      rw [← hJ]
      exact hW₁' i
    · intro j hJ i
      rw [Fin.lastCases_castSucc, Option.some.injEq] at hJ
      rw [← hJ]
      exact hW₁ j' i
  · intro J
    refine Fin.lastCases ?_ (fun j' => ?_) J
    · intro j hJ
      rw [Fin.lastCases_last, Option.some.injEq] at hJ
      rw [← hJ]
      exact hb₁'
    · intro j hJ
      rw [Fin.lastCases_castSucc, Option.some.injEq] at hJ
      rw [← hJ]
      exact hb₁ j'
  · intro K k hK j
    rw [Option.some.injEq] at hK
    subst hK
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Option.some.injEq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hj : j₀ = j
    · subst hj
      rw [if_pos rfl]
      exact hsplit K
    · rw [if_neg hj, add_zero]
      exact hW₂ K j (Ne.symm hj)
  · intro K k hK
    rw [Option.some.injEq] at hK
    rw [← hK, hb₂]
  · intro k
    simp only [Option.some.injEq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hw₃]
  · intro J
    refine Fin.lastCases ?_ (fun j' => ?_) J
    · intro hJ
      rw [Fin.lastCases_last] at hJ
      exact (Option.some_ne_none _ hJ).elim
    · intro hJ
      rw [Fin.lastCases_castSucc] at hJ
      exact (Option.some_ne_none _ hJ).elim
  · intro K hK
    exact (Option.some_ne_none _ hK).elim

section Solutions

variable [NeZero N]

/-- `big` is an expansion (zero padding, duplication with split outgoing weights, and their
compositions) of an exact network of a strictly smaller architecture. -/
def IsExpandedSolution {H₁ H₂ : ℕ} (big : Network N H₁ H₂) : Prop :=
  ∃ (h₁ h₂ : ℕ) (small : Network N h₁ h₂) (φ₁ : Fin H₁ → Option (Fin h₁))
    (φ₂ : Fin H₂ → Option (Fin h₂)),
    h₁ ≤ H₁ ∧ h₂ ≤ H₂ ∧ (h₁ < H₁ ∨ h₂ < H₂) ∧ (∀ x, small.eval x = Maximum N x) ∧
      IsExpansionOf big small φ₁ φ₂

theorem IsExpandedSolution.exact {H₁ H₂ : ℕ} {big : Network N H₁ H₂}
    (h : IsExpandedSolution big) : ∀ x, big.eval x = Maximum N x := by
  obtain ⟨h₁, h₂, small, φ₁, φ₂, -, -, -, hsmall, hexp⟩ := h
  exact fun x => (hexp.eval_eq x).trans (hsmall x)

theorem IsExpandedSolution.hasMergeableOrRedundantNeuron {H₁ H₂ : ℕ} {big : Network N H₁ H₂}
    (h : IsExpandedSolution big) : HasMergeableOrRedundantNeuron big := by
  obtain ⟨h₁, h₂, small, φ₁, φ₂, -, -, hlt, -, hexp⟩ := h
  exact hexp.hasMergeableOrRedundantNeuron hlt

/-- Every padded solution is an expanded solution. -/
theorem _root_.MaxCaterpillar.Fiber.Padding.IsPaddedSolution.isExpandedSolution {H₁ H₂ : ℕ}
    {big : Network N H₁ H₂} (h : IsPaddedSolution big) : IsExpandedSolution big := by
  obtain ⟨h₁, h₂, small, e₁, e₂, hlt, hsmall, hpad⟩ := h
  refine ⟨h₁, h₂, small, _, _, ?_, ?_, hlt, hsmall, hpad.isExpansionOf⟩
  · simpa using Fintype.card_le_of_embedding e₁
  · simpa using Fintype.card_le_of_embedding e₂

/-- **Intrinsic formulation.** A component of the symmetry quotient is reducible iff it
contains (the class of) an expansion of an exact network of a strictly smaller
architecture. -/
theorem isReducibleComponent_iff_expanded
    (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, IsExpandedSolution net.val ∧
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C := by
  constructor
  · intro h
    obtain ⟨net, hpad, hC⟩ := (isReducibleComponent_iff_padded C).mp h
    exact ⟨net, hpad.isExpandedSolution, hC⟩
  · rintro ⟨net, hexp, hC⟩
    exact (isReducibleComponent_iff_mergeableOrRedundant C).mpr
      ⟨net, hexp.hasMergeableOrRedundantNeuron, hC⟩

/-- Raw-fiber version. -/
theorem isReducibleRawComponent_iff_expanded
    (C : ConnectedComponents (ExactFiber N h₁ h₂)) :
    IsReducibleRawComponent C ↔ ∃ net : ExactFiber N h₁ h₂, IsExpandedSolution net.val ∧
      (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C := by
  constructor
  · intro h
    obtain ⟨net, hpad, hC⟩ := (isReducibleRawComponent_iff_padded C).mp h
    exact ⟨net, hpad.isExpandedSolution, hC⟩
  · rintro ⟨net, hexp, hC⟩
    exact (isReducibleRawComponent_iff_mergeableOrRedundant C).mpr
      ⟨net, hexp.hasMergeableOrRedundantNeuron, hC⟩

end Solutions

end MaxCaterpillar.Fiber.Padding.Strong
