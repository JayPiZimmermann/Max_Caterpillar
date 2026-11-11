import research.sN.fiber_padding.Max465

/-! # Max4 at other widths: what the (6,5) theorem implies, and elementary general facts

* `PairedFirstRows` : the paired first-matrix condition stated for a bare `6 × 4` matrix, so
  that it makes sense for every second width.
* `pairedFirstRows_of_exact_of_le_four` : every exact `Network 4 6 h₂` with `h₂ ≤ 4`
  (in particular every exact (6,3) and (6,4) network) has a paired first matrix.
* `max4_6_3_no_removable`, `max4_6_3_no_reducible_component` : at the minimal widths (6,3)
  no exact network has a removable neuron.
* `max4_exists_reducible_component_succ_second`,
  `max4_exists_reducible_component_succ_first` : every non-minimal Max4 architecture has at
  least one reducible component.
* `max4_6_4_removable_is_second` : at (6,4) a removable neuron is a second-hidden-layer
  neuron and deleting it gives an exact (6,3) network.

NOT proved here: connectedness of the (6,4) quotient, reducibility of every (6,4)
component, existence of irreducible components at any architecture other than (6,5).
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Padding

open BigOperators MaxCaterpillar.Fiber.Count65 MaxCaterpillar.Fiber.Count65.SectorQuotient

/-- The paired first-matrix condition for a bare `6 × 4` matrix: up to positive row
scalings and row/column permutations it is `pairedRows a b c d` with `a d - b c ≠ 0`. -/
def PairedFirstRows (W : Fin 6 → Fin 4 → ℝ) : Prop :=
  ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧
    ∃ s : Fin 6 → ℝ, (∀ j, 0 < s j) ∧
    ∃ p : Equiv.Perm (Fin 6), ∃ q : Equiv.Perm (Fin 4),
      ∀ j i, W j i = s j * pairedRows a b c d (p j) (q i)

theorem pairedFirstMatrixForm_iff (net : Network 4 6 5) :
    PairedFirstMatrixForm net ↔ PairedFirstRows net.W₁ := Iff.rfl

private theorem pairedFirstRows_aux {n : ℕ} (he : n = 5) (big : Network 4 6 n)
    (hbig : ∀ x, big.eval x = Maximum 4 x) (k : Fin n) (hk : big.w₃ k = 0) :
    PairedFirstRows big.W₁ := by
  subst he
  exact paired_of_secondOutDead big hbig k hk

/-- **Every exact Max4 network of widths (6,h₂) with `h₂ ≤ 4` has a paired first matrix.**
(Only `h₂ = 3` and `h₂ = 4` are inhabited.) The mixed and star first matrices need five
second-hidden-layer neurons. -/
theorem pairedFirstRows_of_exact_of_le_four {h₂ : ℕ} (hle : h₂ ≤ 4) (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x) : PairedFirstRows net.W₁ := by
  have hpos : 0 < 5 - h₂ := Nat.sub_pos_of_lt (Nat.lt_succ_of_le hle)
  have he : h₂ + (5 - h₂) = 5 := Nat.add_sub_cancel' (hle.trans (by norm_num))
  have h := pairedFirstRows_aux he (net.padSecond (5 - h₂))
    (fun x => (Network.padSecond_eval _ net x).trans (hnet x))
    (Fin.natAdd h₂ ⟨0, hpos⟩)
    (by
      change Fin.append net.w₃ (fun _ : Fin (5 - h₂) => (0 : ℝ)) (Fin.natAdd h₂ ⟨0, hpos⟩) = 0
      rw [Fin.append_right])
  exact h

theorem max4_6_4_paired (net : Network 4 6 4) (hnet : ∀ x, net.eval x = Maximum 4 x) :
    PairedFirstRows net.W₁ :=
  pairedFirstRows_of_exact_of_le_four le_rfl net hnet

theorem max4_6_3_paired (net : Network 4 6 3) (hnet : ∀ x, net.eval x = Maximum 4 x) :
    PairedFirstRows net.W₁ :=
  pairedFirstRows_of_exact_of_le_four (by norm_num) net hnet

/-- There is no exact `Network 4 6 4` whose first matrix is a mixed first matrix. -/
theorem max4_6_4_not_mixed (net : Network 4 6 4) (hnet : ∀ x, net.eval x = Maximum 4 x)
    (t : ℝ) (ht : 0 < t) (c : Fin 6 → ℝ) (hc : ∀ j, 0 < c j) (p : Equiv.Perm (Fin 6))
    (q : Equiv.Perm (Fin 4)) (hW : ∀ j i, net.W₁ j i = c j * Mixed65.firstRows t (p j) (q i)) :
    False := by
  have hm : Mixed65.FirstMatrixForm (net.padSecond 1) := ⟨t, ht, c, hc, p, q, hW⟩
  exact not_paired_of_mixedFirstMatrixForm _ hm (max4_6_4_paired net hnet)

/-- There is no exact `Network 4 6 4` whose first matrix is a star first matrix. -/
theorem max4_6_4_not_star (net : Network 4 6 4) (hnet : ∀ x, net.eval x = Maximum 4 x)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (c : Fin 6 → ℝ) (hc : ∀ j, 0 < c j)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (hW : ∀ j i, net.W₁ j i = c j * Star65.firstRows r (p j) (q i)) : False := by
  have hs : StarFirstMatrixForm (net.padSecond 1) := ⟨r, hr, hr1, c, hc, p, q, hW⟩
  exact not_paired_of_starFirstMatrixForm _ hs (max4_6_4_paired net hnet)

/-! ## The minimal architecture -/

/-- An exact Max4 network with three second-hidden-layer neurons has no removable
second-hidden-layer neuron. -/
theorem not_secondRemovable_of_exact {h₁ : ℕ} (net : Network 4 h₁ 3)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (k : Fin 3) : ¬ SecondRemovable net k := by
  intro hk
  have h := Frontier.second_width_ge_three (N := 4) (by norm_num) (removeSecond (h₂ := 2) net k)
    (fun x => (removeSecond_eval net k hk x).trans (hnet x))
  exact absurd h (by norm_num)

/-- At the minimal widths (6,3) no exact network has a removable hidden neuron. -/
theorem max4_6_3_no_removable (net : Network 4 6 3) (hnet : ∀ x, net.eval x = Maximum 4 x) :
    ¬ HasRemovableNeuron net := by
  rintro (⟨j, hj⟩ | ⟨k, hk⟩)
  · exact not_firstRemovable_of_exact net hnet j hj
  · exact not_secondRemovable_of_exact net hnet k hk

theorem max4_6_3_no_reducible_component (C : ConnectedComponents (SymmetryQuotient 4 6 3)) :
    ¬ IsReducibleComponent C := by
  rintro ⟨net, hrem, -⟩
  exact max4_6_3_no_removable net.val net.property hrem

/-! ## Non-minimal architectures always have a reducible component -/

/-- Every architecture `(h₁, h₂ + 1)` with `6 ≤ h₁`, `3 ≤ h₂` has a reducible component. -/
theorem max4_exists_reducible_component_succ_second {h₁ h₂ : ℕ} (h1 : 6 ≤ h₁) (h2 : 3 ≤ h₂) :
    ∃ C : ConnectedComponents (SymmetryQuotient 4 h₁ (h₂ + 1)), IsReducibleComponent C := by
  obtain ⟨net, hnet⟩ := Frontier.max4_widths_iff.mpr ⟨h1, h2⟩
  let big : ExactFiber 4 h₁ (h₂ + 1) :=
    ⟨net.padSecond 1, fun x => (Network.padSecond_eval 1 net x).trans (hnet x)⟩
  refine ⟨_, big, Or.inr ⟨Fin.natAdd h₂ 0, Or.inl ?_⟩, rfl⟩
  change Fin.append net.w₃ (fun _ : Fin 1 => (0 : ℝ)) (Fin.natAdd h₂ 0) = 0
  rw [Fin.append_right]

/-- Every architecture `(h₁ + 1, h₂)` with `6 ≤ h₁`, `3 ≤ h₂` has a reducible component. -/
theorem max4_exists_reducible_component_succ_first {h₁ h₂ : ℕ} (h1 : 6 ≤ h₁) (h2 : 3 ≤ h₂) :
    ∃ C : ConnectedComponents (SymmetryQuotient 4 (h₁ + 1) h₂), IsReducibleComponent C := by
  obtain ⟨net, hnet⟩ := Frontier.max4_widths_iff.mpr ⟨h1, h2⟩
  let big : ExactFiber 4 (h₁ + 1) h₂ :=
    ⟨net.padFirst 1, fun x => (Network.padFirst_eval 1 net x).trans (hnet x)⟩
  refine ⟨_, big, Or.inl ⟨Fin.natAdd h₁ 0, Or.inl fun k => ?_⟩, rfl⟩
  change Fin.append (net.W₂ k) (fun _ : Fin 1 => (0 : ℝ)) (Fin.natAdd h₁ 0) = 0
  rw [Fin.append_right]

/-! ## Widths (6,4) -/

/-- At widths (6,4), a removable hidden neuron of an exact network is a
second-hidden-layer neuron, and deleting it leaves an exact (6,3) network. -/
theorem max4_6_4_removable_is_second (net : Network 4 6 4)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (h : HasRemovableNeuron net) :
    ∃ k : Fin 4, SecondRemovable net k ∧
      ∀ x, (removeSecond (h₂ := 3) net k).eval x = Maximum 4 x := by
  rcases h with ⟨j, hj⟩ | ⟨k, hk⟩
  · exact (not_firstRemovable_of_exact net hnet j hj).elim
  · exact ⟨k, hk, fun x => (removeSecond_eval net k hk x).trans (hnet x)⟩

/-- The (6,4) quotient has at least one reducible component. -/
theorem max4_6_4_exists_reducible_component :
    ∃ C : ConnectedComponents (SymmetryQuotient 4 6 4), IsReducibleComponent C :=
  max4_exists_reducible_component_succ_second (h₁ := 6) (h₂ := 3) le_rfl le_rfl

#print axioms pairedFirstRows_of_exact_of_le_four
#print axioms max4_6_4_paired
#print axioms max4_6_3_paired
#print axioms max4_6_4_not_mixed
#print axioms max4_6_4_not_star
#print axioms max4_6_3_no_removable
#print axioms max4_6_3_no_reducible_component
#print axioms max4_exists_reducible_component_succ_second
#print axioms max4_exists_reducible_component_succ_first
#print axioms max4_6_4_removable_is_second
#print axioms max4_6_4_exists_reducible_component

end MaxCaterpillar.Fiber.Padding
