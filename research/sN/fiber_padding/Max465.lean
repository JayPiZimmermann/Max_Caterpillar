import research.sN.fiber_padding.Paths
import MaxCaterpillar.Fiber.Count65.GlobalComponents
import MaxCaterpillar.Frontier.Main

/-! # Reducible components of the exact Max4 fiber at widths (6,5)

Main results (all for the ordinary model `Network 4 6 5`, arbitrary biases, every real input):

* `paired_of_hasRemovableNeuron` : an exact network with a removable hidden neuron (under
  either convention) has a paired first matrix. Equivalently
  (`not_hasRemovableNeuron_of_mixed`, `not_hasRemovableNeuron_of_star`) no exact network with
  a mixed or star first matrix has a removable hidden neuron.
* `isReducibleComponent_iff_eq_pairedComponent` : a connected component of
  `SymmetryQuotient 4 6 5` is reducible iff it is `pairedComponent`.
* `max4_6_5_exactly_one_reducible_component`, `max4_6_5_irreducible_component_count` :
  exactly one of the 65 components is reducible, exactly 64 are irreducible.
* `max4_6_5_not_every_component_reducible` : the answer to the question is NO.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Padding

open BigOperators MaxCaterpillar.Fiber.Count65 MaxCaterpillar.Fiber.Count65.SectorQuotient

/-! ## First hidden layer: no removable neuron at width six -/

/-- An exact Max4 network with six first-hidden-layer neurons has no removable
first-hidden-layer neuron: deleting it would give an exact network of first width five. -/
theorem not_firstRemovable_of_exact {h₂ : ℕ} (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (j : Fin 6) : ¬ FirstRemovable net j := by
  intro hj
  have h := Frontier.first_width_ge_six_max4 (removeFirst (h₁ := 5) net j)
    (fun x => (removeFirst_eval net j hj x).trans (hnet x))
  exact absurd h (by norm_num)

/-! ## Normalizing the first matrix without touching the output weights -/

/-- If the first matrix of an exact network is a positively row-scaled, row- and
column-permuted copy of `f`, then some exact network has first matrix exactly `f` and the
same output weights. -/
theorem exists_exact_first_eq {N h₁ h₂ : ℕ} [NeZero N] (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) (f : Fin h₁ → Fin N → ℝ)
    (c : Fin h₁ → ℝ) (hc : ∀ j, 0 < c j) (p : Equiv.Perm (Fin h₁)) (q : Equiv.Perm (Fin N))
    (hW : ∀ j i, net.W₁ j i = c j * f (p j) (q i)) :
    ∃ net' : Network N h₁ h₂, (∀ x, net'.eval x = Maximum N x) ∧ net'.W₁ = f ∧
      net'.w₃ = net.w₃ := by
  refine ⟨permuteInputs (permuteHidden (scaleFirst net (fun j => (c j)⁻¹)) p.symm
    (Equiv.refl _)) q.symm, ?_, ?_, rfl⟩
  · intro x
    rw [permuteInputs_eval, permuteHidden_eval,
      scaleFirst_eval net _ (fun j => inv_pos.mpr (hc j)), hnet]
    exact maximum_permute q.symm.symm x
  · funext j i
    change (c (p.symm j))⁻¹ * net.W₁ (p.symm j) (q.symm i) = f j i
    rw [hW, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← mul_assoc,
      inv_mul_cancel (hc (p.symm j)).ne', one_mul]

/-! ## Second hidden layer: removable neurons force the paired sector -/

/-- In an exact network with a mixed first matrix all five output weights are nonzero. -/
theorem output_ne_zero_of_mixed (net : Network 4 6 5) (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hm : Mixed65.FirstMatrixForm net) (k : Fin 5) : net.w₃ k ≠ 0 := by
  obtain ⟨t, ht, c, hc, p, q, hW⟩ := hm
  obtain ⟨net', hnet', hW', hw⟩ := exists_exact_first_eq net hnet (Mixed65.firstRows t) c hc p q hW
  rw [← hw]
  exact (PhysicalExtraction.physical_output_sign_counts net' t ht hW' hnet').2.2 k

/-- In an exact network with a star first matrix all five output weights are nonzero. -/
theorem output_ne_zero_of_star (net : Network 4 6 5) (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hs : StarFirstMatrixForm net) (k : Fin 5) : net.w₃ k ≠ 0 := by
  obtain ⟨r, hr, hr1, c, hc, p, q, hW⟩ := hs
  obtain ⟨net', hnet', hW', hw⟩ := exists_exact_first_eq net hnet (Star65.firstRows r) c hc p q hW
  rw [← hw]
  exact (Star.physical_output_sign_counts net' r hr hr1 hW' hnet').2.2 k

/-- An exact network one of whose output weights vanishes has a paired first matrix. -/
theorem paired_of_secondOutDead (net : Network 4 6 5) (hnet : ∀ x, net.eval x = Maximum 4 x)
    (k : Fin 5) (hk : SecondOutDead net k) : PairedFirstMatrixForm net := by
  rcases max4_first_matrix_trichotomy net hnet with hp | hm | hs
  · exact hp
  · exact (output_ne_zero_of_mixed net hnet hm k hk).elim
  · exact (output_ne_zero_of_star net hnet hs k hk).elim

/-- **Key pointwise statement.** Every exact `Network 4 6 5` with a removable hidden neuron
(zero outgoing weights, or zero incoming weights and zero bias) has a paired first matrix. -/
theorem paired_of_hasRemovableNeuron (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (h : HasRemovableNeuron net) :
    PairedFirstMatrixForm net := by
  rcases h with ⟨j, hj⟩ | ⟨k, hk | hk⟩
  · exact (not_firstRemovable_of_exact net hnet j hj).elim
  · exact paired_of_secondOutDead net hnet k hk
  · -- zero incoming weights and bias: set the outgoing weight to zero; the first matrix
    -- does not change.
    have hp : PairedFirstMatrixForm (scaleSecondOut net k 0) :=
      paired_of_secondOutDead (scaleSecondOut net k 0)
        (fun x => (scaleSecondOut_eval net k hk 0 x).trans (hnet x)) k
        (by change mult k 0 k * net.w₃ k = 0; rw [mult_self, zero_mul])
    exact hp

/-- No exact network with a mixed first matrix has a removable hidden neuron. -/
theorem not_hasRemovableNeuron_of_mixed (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (hm : Mixed65.FirstMatrixForm net) :
    ¬ HasRemovableNeuron net := fun h =>
  not_paired_of_mixedFirstMatrixForm net hm (paired_of_hasRemovableNeuron net hnet h)

/-- No exact network with a star first matrix has a removable hidden neuron. -/
theorem not_hasRemovableNeuron_of_star (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (hs : StarFirstMatrixForm net) :
    ¬ HasRemovableNeuron net := fun h =>
  not_paired_of_starFirstMatrixForm net hs (paired_of_hasRemovableNeuron net hnet h)

/-! ## The paired sector lies in one component of the symmetry quotient -/

/-- The map of symmetry quotients induced by forgetting the zero-bias condition. -/
def includeQuotient : ZeroBiasSymmetryQuotient 4 6 5 → SymmetryQuotient 4 6 5 :=
  Quotient.map' includeZeroBias (fun _ _ h => h)

theorem continuous_includeQuotient : Continuous includeQuotient :=
  continuous_includeZeroBias.quotient_map' _

/-- The padded minimal network: the width-(6,3) network `maxFourNet` with two additional
second-hidden-layer neurons all of whose incident parameters vanish. -/
noncomputable abbrev paddedPoint : ExactFiber 4 6 5 := Mixed65.paddedMinimalPoint

/-- The component of the symmetry quotient containing the padded minimal network. -/
noncomputable def pairedComponent : ConnectedComponents (SymmetryQuotient 4 6 5) :=
  ((quotientMk paddedPoint : SymmetryQuotient 4 6 5) :
    ConnectedComponents (SymmetryQuotient 4 6 5))

/-- Every exact network with a paired first matrix lies in the component of the padded
minimal network. -/
theorem component_eq_pairedComponent_of_paired (net : ExactFiber 4 6 5)
    (hp : PairedFirstMatrixForm net.val) :
    ((quotientMk net : SymmetryQuotient 4 6 5) :
      ConnectedComponents (SymmetryQuotient 4 6 5)) = pairedComponent := by
  -- remove the biases along a path inside the exact fiber
  have h1 := quotient_component_eq_of_joined (a := net) (b := zeroBiasFiber net) ⟨biasPath net⟩
  rw [h1]
  let z : ZeroBiasFiber 4 6 5 := zeroBiasRetraction net
  have hz : Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) z ∈ Paired.quotientSector :=
    ⟨z, hp, rfl⟩
  have hw : AtLeast65.pairedWitness ∈ Paired.quotientSector :=
    ⟨AtLeast65.pairedWitnessZeroPoint, AtLeast65.paddedMinimalPoint_paired, rfl⟩
  have hj : Joined (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) z) AtLeast65.pairedWitness :=
    (Paired.isPathConnected_quotientSector.joinedIn _ hz _ hw).joined
  have hj' : Joined (includeQuotient (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) z))
      (includeQuotient AtLeast65.pairedWitness) :=
    ⟨hj.somePath.map continuous_includeQuotient⟩
  exact component_eq_of_joined hj'

/-- The padded minimal network has a removable (indeed zero) second-hidden-layer neuron. -/
theorem paddedPoint_hasZeroNeuron : HasZeroNeuron paddedPoint.val := by
  refine Or.inr ⟨Fin.natAdd 3 (0 : Fin 2), ?_, ?_, ?_⟩
  · change Fin.append Frontier.maxFourNet.w₃ (fun _ : Fin 2 => (0 : ℝ)) (Fin.natAdd 3 0) = 0
    rw [Fin.append_right]
  · intro j
    change Fin.append Frontier.maxFourNet.W₂ (fun (_ : Fin 2) (_ : Fin 6) => (0 : ℝ))
      (Fin.natAdd 3 0) j = 0
    rw [Fin.append_right]
  · change Fin.append Frontier.maxFourNet.b₂ (fun _ : Fin 2 => (0 : ℝ)) (Fin.natAdd 3 0) = 0
    rw [Fin.append_right]

/-- The padded minimal network is a padded solution in the sense of `IsPaddedSolution`. -/
theorem paddedPoint_isPaddedSolution : IsPaddedSolution paddedPoint.val :=
  (isPaddedSolution_iff _).mpr ⟨paddedPoint.property, paddedPoint_hasZeroNeuron.hasRemovableNeuron⟩

/-! ## Main theorem at (6,5) -/

/-- **Main theorem.** A connected component of the symmetry quotient of the exact Max4
fiber at widths (6,5) is reducible if and only if it is the component of the padded
minimal network (the paired component). -/
theorem isReducibleComponent_iff_eq_pairedComponent
    (C : ConnectedComponents (SymmetryQuotient 4 6 5)) :
    IsReducibleComponent C ↔ C = pairedComponent := by
  constructor
  · rintro ⟨net, hrem, rfl⟩
    exact component_eq_pairedComponent_of_paired net
      (paired_of_hasRemovableNeuron net.val net.property hrem)
  · rintro rfl
    exact ⟨paddedPoint, paddedPoint_hasZeroNeuron.hasRemovableNeuron, rfl⟩

/-- The same theorem with every definition unfolded: there is a component `C₀` such that a
component `C` contains the class of an exact network with a removable hidden neuron iff
`C = C₀`. -/
theorem max4_6_5_exactly_one_reducible_component :
    ∃ C₀ : ConnectedComponents (SymmetryQuotient 4 6 5),
      ∀ C : ConnectedComponents (SymmetryQuotient 4 6 5),
        (∃ net : Network 4 6 5, ∃ hnet : ∀ x, net.eval x = Maximum 4 x,
          ((∃ j, (∀ k, net.W₂ k j = 0) ∨ ((∀ i, net.W₁ j i = 0) ∧ net.b₁ j = 0)) ∨
            ∃ k, net.w₃ k = 0 ∨ ((∀ j, net.W₂ k j = 0) ∧ net.b₂ k = 0)) ∧
          ((quotientMk ⟨net, hnet⟩ : SymmetryQuotient 4 6 5) :
            ConnectedComponents (SymmetryQuotient 4 6 5)) = C) ↔ C = C₀ := by
  refine ⟨pairedComponent, fun C => ?_⟩
  rw [← isReducibleComponent_iff_eq_pairedComponent]
  constructor
  · rintro ⟨net, hnet, hrem, hC⟩
    exact ⟨⟨net, hnet⟩, hrem, hC⟩
  · rintro ⟨net, hrem, hC⟩
    exact ⟨net.val, net.property, hrem, hC⟩

/-- A component is irreducible iff none of the exact networks whose class lies in it has a
removable hidden neuron. -/
theorem not_isReducibleComponent_iff {N h₁ h₂ : ℕ} [NeZero N]
    (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    ¬ IsReducibleComponent C ↔ ∀ net : ExactFiber N h₁ h₂,
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C → ¬ HasRemovableNeuron net.val := by
  constructor
  · intro h net hC hrem
    exact h ⟨net, hrem, hC⟩
  · rintro h ⟨net, hrem, hC⟩
    exact h net hC hrem

/-- Exactly 64 components of the (6,5) quotient are irreducible. -/
theorem max4_6_5_irreducible_component_count :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) // ¬ IsReducibleComponent C}
      = 64 := by
  let e := Count65.fullComponentsEquiv65
  have e' : {C : ConnectedComponents (SymmetryQuotient 4 6 5) // ¬ IsReducibleComponent C} ≃
      {i : Fin 65 // i ≠ e pairedComponent} :=
    e.subtypeEquiv (fun C => by
      rw [isReducibleComponent_iff_eq_pairedComponent]
      exact (e.apply_eq_iff_eq).not.symm)
  rw [Nat.card_congr (e'.trans (finSuccAboveEquiv (e pairedComponent)).symm.toEquiv)]
  simp

/-- Exactly one component of the (6,5) quotient is reducible. -/
theorem max4_6_5_reducible_component_count :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) // IsReducibleComponent C}
      = 1 := by
  have e : {C : ConnectedComponents (SymmetryQuotient 4 6 5) // IsReducibleComponent C} ≃
      Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨pairedComponent,
        (isReducibleComponent_iff_eq_pairedComponent _).mpr rfl⟩
      left_inv := fun C => Subtype.ext
        ((isReducibleComponent_iff_eq_pairedComponent _).mp C.property).symm
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp

/-- Fully unfolded count: exactly 64 components contain only classes of exact networks
without any removable hidden neuron. -/
theorem max4_6_5_exactly_64_components_without_removable_neuron :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∀ (net : Network 4 6 5) (hnet : ∀ x, net.eval x = Maximum 4 x),
        ((quotientMk ⟨net, hnet⟩ : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C →
        ¬ ((∃ j, (∀ k, net.W₂ k j = 0) ∨ ((∀ i, net.W₁ j i = 0) ∧ net.b₁ j = 0)) ∨
            ∃ k, net.w₃ k = 0 ∨ ((∀ j, net.W₂ k j = 0) ∧ net.b₂ k = 0))} = 64 := by
  rw [← max4_6_5_irreducible_component_count]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ?_)
  rw [not_isReducibleComponent_iff]
  constructor
  · intro h net hC
    exact h net.val net.property hC
  · intro h net hnet hC
    exact h ⟨net, hnet⟩ hC

/-- **Answer to the question for Max4: NO.** At the non-minimal widths (6,5) not every
connected component of the exact fiber modulo symmetries contains a padded smaller
solution. -/
theorem max4_6_5_not_every_component_reducible :
    ¬ ∀ C : ConnectedComponents (SymmetryQuotient 4 6 5), IsReducibleComponent C := by
  intro h
  have h64 := max4_6_5_irreducible_component_count
  have hempty : IsEmpty {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ¬ IsReducibleComponent C} := ⟨fun C => C.property (h C.val)⟩
  rw [Nat.card_of_isEmpty] at h64
  exact absurd h64 (by norm_num)

/-- The same negative answer for the exact fiber before the symmetry quotient. -/
theorem max4_6_5_not_every_raw_component_reducible :
    ¬ ∀ C : ConnectedComponents (ExactFiber 4 6 5), IsReducibleRawComponent C := by
  intro h
  apply max4_6_5_not_every_component_reducible
  intro C
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe C
  obtain ⟨net, rfl⟩ := quotientMk_surjective z
  obtain ⟨net', hrem, hC⟩ := h (net : ConnectedComponents (ExactFiber 4 6 5))
  refine ⟨net', hrem, ?_⟩
  have := congrArg (quotientMk_continuous (N := 4) (h₁ := 6) (h₂ := 5)).connectedComponentsMap hC
  exact this

#print axioms paired_of_hasRemovableNeuron
#print axioms not_hasRemovableNeuron_of_mixed
#print axioms not_hasRemovableNeuron_of_star
#print axioms isReducibleComponent_iff_eq_pairedComponent
#print axioms max4_6_5_exactly_one_reducible_component
#print axioms max4_6_5_irreducible_component_count
#print axioms max4_6_5_reducible_component_count
#print axioms max4_6_5_exactly_64_components_without_removable_neuron
#print axioms max4_6_5_not_every_component_reducible
#print axioms max4_6_5_not_every_raw_component_reducible

end MaxCaterpillar.Fiber.Padding
