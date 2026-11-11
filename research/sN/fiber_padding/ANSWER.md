# Does every component of a non-minimal exact Max4 fiber contain a padded smaller solution?

**Answer: NO, already at widths (6,5).** At widths (6,5) exactly one of the 65 connected
components of the exact fiber modulo symmetries contains a network with a removable hidden
neuron; the other 64 contain none. (These 64 are the components of networks with non-paired,
i.e. mixed or star, first matrix; the split 32 + 32 is the library's label type and is not
restated here.) The negative answer is proved for the architecture (6,5) only; for no other
non-minimal architecture is the existence of an irreducible component decided here.

Everything in section 1-3 is Lean-verified: the four files compile with
`lake env lean`, contain no `sorry`/`admit`/`native_decide`/`axiom`, and every theorem
listed prints exactly `[propext, Classical.choice, Quot.sound]` under `#print axioms`.
Namespace of all names below: `MaxCaterpillar.Fiber.Padding`.

Files (import chain `Defs -> Paths -> Max465 -> Max4General`):

- `research/sN/fiber_padding/Defs.lean`
- `research/sN/fiber_padding/Paths.lean`
- `research/sN/fiber_padding/Max465.lean`
- `research/sN/fiber_padding/Max4General.lean`

## 1. Definitions (D1), for arbitrary `Network N h₁ h₂`

    def FirstOutDead  net j := ∀ k, net.W₂ k j = 0                       -- zero outgoing weights
    def FirstInDead   net j := (∀ i, net.W₁ j i = 0) ∧ net.b₁ j = 0      -- zero incoming weights and bias
    def SecondOutDead net k := net.w₃ k = 0
    def SecondInDead  net k := (∀ j, net.W₂ k j = 0) ∧ net.b₂ k = 0
    def HasOutDeadNeuron  net := (∃ j, FirstOutDead net j) ∨ ∃ k, SecondOutDead net k      -- convention A
    def HasInDeadNeuron   net := (∃ j, FirstInDead net j) ∨ ∃ k, SecondInDead net k        -- convention B
    def HasRemovableNeuron net := (∃ j, FirstOutDead net j ∨ FirstInDead net j) ∨
                                  ∃ k, SecondOutDead net k ∨ SecondInDead net k            -- A or B
    def HasZeroNeuron net := some neuron is dead under A and B simultaneously

    def IsPaddedSolution big := ∃ h₁ h₂ (small : Network N h₁ h₂) (e₁ : Fin h₁ ↪ Fin H₁) (e₂ : Fin h₂ ↪ Fin H₂),
        (h₁ < H₁ ∨ h₂ < H₂) ∧ (∀ x, small.eval x = Maximum N x) ∧ IsPaddingOf big small e₁ e₂

    def IsReducibleComponent (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :=
      ∃ net : ExactFiber N h₁ h₂, HasRemovableNeuron net.val ∧ ((quotientMk net : _) : ConnectedComponents _) = C

`IsPaddingOf big small e₁ e₂`: all parameters of `small` appear in `big` along the neuron
embeddings and every other hidden neuron of `big` is removable (A or B).

Robustness theorems:

- `isPaddedSolution_iff : IsPaddedSolution big ↔ (∀ x, big.eval x = Maximum N x) ∧ HasRemovableNeuron big`
- `IsPaddingOf.eval_eq`, `removeFirst_eval`, `removeSecond_eval` (deleting a removable neuron keeps the function)
- `hasRemovableNeuron_of_quotientMk_eq` (the notion is well defined on the symmetry quotient)
- `exists_joined_hasZeroNeuron` (a removable neuron becomes a zero neuron along a path inside the exact fiber)
- the conventions agree on components:
  `isReducibleComponent_iff_outDead`, `isReducibleComponent_iff_inDead`,
  `isReducibleComponent_iff_zeroNeuron`, `isReducibleComponent_iff_padded`
  (each: `IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, P net.val ∧ component (quotientMk net) = C`
  with `P` = `HasOutDeadNeuron`, `HasInDeadNeuron`, `HasZeroNeuron`, `IsPaddedSolution`);
  same four statements for components of the fiber before the quotient (`isReducibleRawComponent_iff_*`).

## 2. Main theorem at (6,5) (D2), file `Max465.lean`

    theorem paired_of_hasRemovableNeuron (net : Network 4 6 5)
        (hnet : ∀ x, net.eval x = Maximum 4 x) (h : HasRemovableNeuron net) :
        PairedFirstMatrixForm net

    theorem not_hasRemovableNeuron_of_mixed (net : Network 4 6 5)
        (hnet : ∀ x, net.eval x = Maximum 4 x) (hm : Mixed65.FirstMatrixForm net) : ¬ HasRemovableNeuron net
    theorem not_hasRemovableNeuron_of_star  (net : Network 4 6 5)
        (hnet : ∀ x, net.eval x = Maximum 4 x) (hs : StarFirstMatrixForm net) : ¬ HasRemovableNeuron net

    noncomputable def pairedComponent : ConnectedComponents (SymmetryQuotient 4 6 5) :=
      component of quotientMk (maxFourNet.padSecond 2)

    theorem isReducibleComponent_iff_eq_pairedComponent
        (C : ConnectedComponents (SymmetryQuotient 4 6 5)) :
        IsReducibleComponent C ↔ C = pairedComponent

    theorem max4_6_5_exactly_one_reducible_component :
        ∃ C₀ : ConnectedComponents (SymmetryQuotient 4 6 5),
          ∀ C : ConnectedComponents (SymmetryQuotient 4 6 5),
            (∃ net : Network 4 6 5, ∃ hnet : ∀ x, net.eval x = Maximum 4 x,
              ((∃ j, (∀ k, net.W₂ k j = 0) ∨ ((∀ i, net.W₁ j i = 0) ∧ net.b₁ j = 0)) ∨
                ∃ k, net.w₃ k = 0 ∨ ((∀ j, net.W₂ k j = 0) ∧ net.b₂ k = 0)) ∧
              ((quotientMk ⟨net, hnet⟩ : SymmetryQuotient 4 6 5) :
                ConnectedComponents (SymmetryQuotient 4 6 5)) = C) ↔ C = C₀

    theorem max4_6_5_irreducible_component_count :
        Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) // ¬ IsReducibleComponent C} = 64
    theorem max4_6_5_reducible_component_count :
        Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) // IsReducibleComponent C} = 1

    theorem max4_6_5_exactly_64_components_without_removable_neuron :
        Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
          ∀ (net : Network 4 6 5) (hnet : ∀ x, net.eval x = Maximum 4 x),
            ((quotientMk ⟨net, hnet⟩ : SymmetryQuotient 4 6 5) :
              ConnectedComponents (SymmetryQuotient 4 6 5)) = C →
            ¬ ((∃ j, (∀ k, net.W₂ k j = 0) ∨ ((∀ i, net.W₁ j i = 0) ∧ net.b₁ j = 0)) ∨
                ∃ k, net.w₃ k = 0 ∨ ((∀ j, net.W₂ k j = 0) ∧ net.b₂ k = 0))} = 64

    theorem max4_6_5_not_every_component_reducible :
        ¬ ∀ C : ConnectedComponents (SymmetryQuotient 4 6 5), IsReducibleComponent C
    theorem max4_6_5_not_every_raw_component_reducible :
        ¬ ∀ C : ConnectedComponents (ExactFiber 4 6 5), IsReducibleRawComponent C

Proof route. A removable first-hidden-layer neuron would give an exact (5,5) network
(`Frontier.first_width_ge_six_max4`). A second-hidden-layer neuron with zero incoming
weights and bias can have its output weight set to zero without changing the function or
the first matrix. A zero output weight is impossible over a mixed or star first matrix
(`Count65.PhysicalExtraction.physical_output_sign_counts`,
`Count65.Star.physical_output_sign_counts`, after normalizing the first matrix by
symmetries that do not change `w₃`), so by `Count65.max4_first_matrix_trichotomy` the first
matrix is paired. All paired networks lie in one component
(`Count65.Paired.isPathConnected_quotientSector` plus the bias path), which contains the
padded minimal network `maxFourNet.padSecond 2`.

## 3. Other widths (D3), file `Max4General.lean` -- Lean-verified

    theorem pairedFirstRows_of_exact_of_le_four {h₂ : ℕ} (hle : h₂ ≤ 4) (net : Network 4 6 h₂)
        (hnet : ∀ x, net.eval x = Maximum 4 x) : PairedFirstRows net.W₁
    -- corollaries max4_6_4_paired, max4_6_3_paired, max4_6_4_not_mixed, max4_6_4_not_star:
    -- every exact (6,4) and (6,3) network has a paired first matrix; mixed and star first
    -- matrices have no exact completion with four second-hidden-layer neurons.

    theorem max4_6_3_no_removable (net : Network 4 6 3) (hnet : ∀ x, net.eval x = Maximum 4 x) :
        ¬ HasRemovableNeuron net
    theorem max4_6_3_no_reducible_component (C : ConnectedComponents (SymmetryQuotient 4 6 3)) :
        ¬ IsReducibleComponent C

    theorem max4_exists_reducible_component_succ_second {h₁ h₂ : ℕ} (h1 : 6 ≤ h₁) (h2 : 3 ≤ h₂) :
        ∃ C : ConnectedComponents (SymmetryQuotient 4 h₁ (h₂ + 1)), IsReducibleComponent C
    theorem max4_exists_reducible_component_succ_first {h₁ h₂ : ℕ} (h1 : 6 ≤ h₁) (h2 : 3 ≤ h₂) :
        ∃ C : ConnectedComponents (SymmetryQuotient 4 (h₁ + 1) h₂), IsReducibleComponent C

    theorem max4_6_4_removable_is_second (net : Network 4 6 4)
        (hnet : ∀ x, net.eval x = Maximum 4 x) (h : HasRemovableNeuron net) :
        ∃ k : Fin 4, SecondRemovable net k ∧ ∀ x, (removeSecond (h₂ := 3) net k).eval x = Maximum 4 x

`PairedFirstRows W` is `Count65.PairedFirstMatrixForm` stated for a bare 6 x 4 matrix
(`pairedFirstMatrixForm_iff` is `Iff.rfl`).

## 4. NOT proved (no Lean statement; do not cite as results)

- (6,4): connectivity of the quotient is proved separately and is not part of this
  directory. Together with `max4_6_4_exists_reducible_component` above it makes the
  unique (6,4) component reducible.
- Any architecture other than (6,5) and (6,3): existence or non-existence of irreducible
  components. In particular it is open here whether (6,h₂) for h₂ ≥ 6 or (h₁,5) for
  h₁ ≥ 7 has an irreducible component. Padding a mixed or star (6,5) network produces by
  definition a reducible point, so the (6,5) theorem does not propagate upward.

## 5. Verification record

- Receipt: `Check.lean` in this directory restates the (6,5) results with their exact types;
  compiled on a compute node, exit 0, axioms `propext`, `Classical.choice`, `Quot.sound`
  (`Check.log`).
- An independent audit (2026-11-11) recompiled verbatim copies of these files on a compute
  node, all exit 0. Its working files were removed from the repository afterwards.
