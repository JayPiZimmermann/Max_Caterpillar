# Is the notion of padding strong enough? (research/sN/fiber_padding/strong)

**Answer: yes.** Every way a network can be "secretly smaller" that we could name
(mergeable, dead, constant, linearly dependent, absorbable neurons; duplication with split
outgoing weights) is joined by an explicit path INSIDE the exact fiber to a network with a
strictly zero neuron. Hence "reducible component" does not change under the strong notion,
and at widths (6,5) the 64 non-paired components contain no network with any such degeneracy.
Two proposed items are NOT reductions and have Lean counterexamples (section 4).

Everything in sections 1-4 is Lean-verified: files compile on a compute node (exit 0), no
`sorry`/`admit`/`native_decide`/`axiom`; `Main.lean` restates each headline as
`example : <type> := name` and prints axioms: 27 lines, all exactly
`propext, Classical.choice, Quot.sound` (`Main.log`).
Namespace: `MaxCaterpillar.Fiber.Padding.Strong`. Import chain:
`Semantic -> Strong -> {Max465Strong, Expansion, Counter2} -> Main`.

## 1. Definitions (general `Network N h₁ h₂`)

    act₁ net j x = relu (Σ i, W₁ j i * x i + b₁ j)          -- rfl
    pre₂ net k x = Σ j, W₂ k j * act₁ net j x + b₂ k        -- rfl
    act₂ net k x = relu (pre₂ net k x);   net.eval x = Σ k, w₃ k * act₂ net k x + b₃   -- rfl

Semantic predicates (Semantic.lean):

    FirstDependent net j'  := ∃ c c₀, c j' = 0 ∧ ∀ x, act₁ net j' x = Σ j, c j * act₁ net j x + c₀
    SecondDependent net k' := ∃ c c₀, c k' = 0 ∧ ∀ x, act₂ net k' x = Σ k, c k * act₂ net k x + c₀
    SecondActiveAbsorb net k k' := k ≠ k' ∧ (∀ x, 0 ≤ pre₂ net k x) ∧ (∀ x, 0 ≤ pre₂ net k' x) ∧
        ∃ s M, w₃ k' = s * w₃ k ∧ ∀ x, 0 ≤ pre₂ net k x + s * pre₂ net k' x + M

Weight-level cases (Strong.lean):

    (a) FirstProportional net j j'  := j ≠ j' ∧ ∃ c ≥ 0, (∀ i, W₁ j' i = c * W₁ j i) ∧ b₁ j' = c * b₁ j
        SecondProportional net k k' := k ≠ k' ∧ ∃ c ≥ 0, (∀ j, W₂ k' j = c * W₂ k j) ∧ b₂ k' = c * b₂ k
    (b) FirstNeverActive net j  := ∀ x, Σ i, W₁ j i * x i + b₁ j ≤ 0
        SecondNeverActive net k := ∀ x, pre₂ net k x ≤ 0       -- dead on the range of the features
    (c) FirstZeroRow net j := ∀ i, W₁ j i = 0                  -- any bias
    (d) SecondConstantPre net k := ∃ c₀, ∀ x, pre₂ net k x = c₀   (SecondZeroRow is a special case)
    (e) SecondActiveSameSign net k k' := k ≠ k' ∧ both always active ∧ 0 ≤ w₃ k * w₃ k'

    HasMergeableOrRedundantNeuron net := HasRemovableNeuron net ∨ (∃ j, FirstDependent net j) ∨
        (∃ k, SecondDependent net k) ∨ ∃ k k', SecondActiveAbsorb net k k'
    HasListedDegeneracy net := HasRemovableNeuron ∨ (a) ∨ (a) ∨ (b) ∨ (b) ∨ (c) ∨ (d) ∨ (e)

`HasListedDegeneracy.hasMergeableOrRedundantNeuron : HasListedDegeneracy net → HasMergeableOrRedundantNeuron net`.

## 2. The user's conjecture, general N, h₁, h₂ (Strong.lean)

    theorem exists_joined_hasZeroNeuron_of_mergeableOrRedundant [NeZero N] (net : ExactFiber N h₁ h₂)
        (h : HasMergeableOrRedundantNeuron net.val) :
        ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧ HasZeroNeuron net'.val
    theorem exists_joined_hasZeroNeuron_of_listedDegeneracy   -- same with HasListedDegeneracy

    theorem isReducibleComponent_iff_mergeableOrRedundant (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
        IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasMergeableOrRedundantNeuron net.val ∧
          ((quotientMk net : SymmetryQuotient N h₁ h₂) : ConnectedComponents _) = C
    theorem isReducibleComponent_iff_listedDegeneracy          -- same with HasListedDegeneracy
    theorem isReducibleRawComponent_iff_mergeableOrRedundant   -- raw fiber, no quotient
    theorem isReducibleRawComponent_iff_listedDegeneracy

Paths (Semantic.lean): `transferFirst` (move outgoing column of j' to the other neurons and
to b₂), `transferSecond` (move w₃ k' to the others and to b₃), `absorbSecond` (k absorbs the
affine function of k'; exact for t in [0,1]); each with `_eval`, `continuous_`, `_zero`,
`_one_outDead`.

## 3. Intrinsic formulation (Expansion.lean)

`IsExpansionOf big small φ₁ φ₂` with `φ₁ : Fin H₁ → Option (Fin h₁)`, `φ₂ : Fin H₂ → Option (Fin h₂)`:
a neuron with `φ = some j` is a copy of `j` (same incoming row and bias; for a second-layer
copy K of k: `Σ_{J copy of j} big.W₂ K J = small.W₂ k j`), the outgoing weights of the copies
of one neuron sum to the original (`Σ_{K copy of k} big.w₃ K = small.w₃ k`), a neuron with
`φ = none` is removable. `IsExpandedSolution big` := expansion of an exact network of widths
`h₁ ≤ H₁, h₂ ≤ H₂`, one strict.

    theorem IsExpansionOf.eval_eq : IsExpansionOf big small φ₁ φ₂ → ∀ x, big.eval x = small.eval x
    theorem IsPaddingOf.isExpansionOf : IsPaddingOf big small e₁ e₂ →
        IsExpansionOf big small (Function.partialInv e₁) (Function.partialInv e₂)
    theorem isExpansionOf_duplicateFirst   -- duplicating a first-layer neuron with split outgoing column is an instance
    theorem IsExpandedSolution.exact, IsExpandedSolution.hasMergeableOrRedundantNeuron
    theorem IsPaddedSolution.isExpandedSolution
    theorem isReducibleComponent_iff_expanded (C) :
        IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, IsExpandedSolution net.val ∧ component (quotientMk net) = C
    theorem isReducibleRawComponent_iff_expanded

## 4. Max4 corollaries and counterexamples (Max465Strong.lean, Counter2.lean, Main.lean)

    theorem not_mergeableOrRedundant_of_component_ne (net : ExactFiber 4 6 5)
        (hC : component (quotientMk net) ≠ pairedComponent) : ¬ HasMergeableOrRedundantNeuron net.val
    theorem not_listedDegeneracy_of_component_ne        -- same, HasListedDegeneracy
    theorem no_degeneracy_unfolded_of_component_ne      -- nine raw-weight conjuncts, see file
    theorem Main.not_expandedSolution_of_component_ne   -- ¬ IsExpandedSolution net.val
    theorem Main.not_removable_of_joined_of_component_ne (net net') (hC) (hj : Joined net net') :
        ¬ HasRemovableNeuron net'.val
    theorem max4_6_5_exactly_one_component_with_mergeableOrRedundant :
        ∃ C₀, ∀ C, (∃ net : ExactFiber 4 6 5, HasMergeableOrRedundantNeuron net.val ∧ component = C) ↔ C = C₀
    theorem max4_6_5_mergeableOrRedundant_component_count : Nat.card {C // ∃ net, HasMergeableOrRedundantNeuron net.val ∧ ...} = 1
    theorem max4_6_5_exactly_64_components_without_mergeableOrRedundant :
        Nat.card {C // ∀ net : ExactFiber 4 6 5, component = C → ¬ HasMergeableOrRedundantNeuron net.val} = 64
    theorem max4_6_5_listedDegeneracy_component_count (= 1),
            max4_6_5_exactly_64_components_without_listedDegeneracy (= 64),
            Main.max4_6_5_exactly_64_components_without_expandedSolution (= 64)
    theorem max4_6_5_exists_raw_component_without_mergeableOrRedundant   -- raw fiber, existence only
    theorem max4_6_3_no_mergeableOrRedundant (net : Network 4 6 3) (hnet) : ¬ HasMergeableOrRedundantNeuron net

Counterexamples (items of (e) that are FALSE as reductions):

    theorem oppositePair_not_reducible : ∃ net : ExactFiber 4 6 3,
        (∃ j j', FirstOppositePair net.val j j') ∧ (∃ k k', SecondOppositePair net.val k k') ∧
        ¬ HasMergeableOrRedundantNeuron net.val ∧ ¬ IsReducibleComponent (component (quotientMk net))
      -- maxFourNet: rows W₁ 3 = -W₁ 2 with columns W₂ · 3 = -W₂ · 2; second-layer rows 1 = -(row 0), w₃ 1 = -w₃ 0
    theorem active_opposite_sign_not_reducible : ∃ net : ExactFiber 2 3 2,
        (∃ k k', k ≠ k' ∧ both always active ∧ w₃ k * w₃ k' < 0) ∧
        ¬ HasMergeableOrRedundantNeuron net.val ∧ ¬ IsReducibleComponent (component (quotientMk net))
      -- max(x₀,x₁) = σ(σ(x₀-x₁)+σ(x₁)) - σ(σ(-x₁)); (3,2) is minimal for N = 2
      -- (max2_3_2_no_removable, no_exact_second_width_one)

## 5. Caveats / not proved

- The numbers 1 and 64 rest on the earlier track (`max4_6_5_reducible_component_count`,
  `max4_6_5_irreducible_component_count`) and on the library equivalence with `Fin 65`.
- "Proportional" means multiple `c ≥ 0` of row AND bias; copies in `IsExpansionOf` are exact
  copies (positive rescaling is one of the quotient symmetries, not part of the definition).
  Duplication in the second hidden layer is covered by the definition (`φ₂`), but only the
  first-layer duplication has an explicit instance lemma.
- Raw fiber at (6,5): only existence of a component without degenerate networks, no count.
- No claim that `HasMergeableOrRedundantNeuron` lists every conceivable reduction. What is
  proved for the 64 components independently of any list: no network joined inside the exact
  fiber to them has a removable neuron (`not_removable_of_joined_of_component_ne`).
- Nothing new about architectures other than (6,5), (6,3) and (N=2: (3,2)).
