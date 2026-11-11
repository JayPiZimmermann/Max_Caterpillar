import research.sN.fiber_padding.strong.Semantic

/-! # The strong notion of a secretly smaller network

Concrete (weight-level) degeneracies of a hidden neuron, each of which implies one of the
semantic predicates of `Semantic.lean`:

* (a) `FirstProportional net j j'`, `SecondProportional net k k'` : the incoming row and the
  bias of the second neuron are a nonnegative multiple of those of the first one;
* (b) `FirstNeverActive net j`, `SecondNeverActive net k` : the preactivation is `≤ 0` at
  every input (for the second hidden layer: on the range of the first-layer features);
* (c) `FirstZeroRow net j` : zero incoming weights, arbitrary bias;
* (d) `SecondConstantPre net k` : the preactivation of a second-hidden-layer neuron is
  constant (e.g. zero incoming weights, arbitrary bias: `SecondZeroRow`);
* (e) `SecondActiveSameSign net k k'` : two second-hidden-layer neurons active at every
  input whose output weights do not have opposite signs.

`HasMergeableOrRedundantNeuron` is the disjunction of `HasRemovableNeuron` and the three
semantic predicates; `HasListedDegeneracy` is the disjunction of the weight-level cases.
Main results: every exact network with such a degeneracy is joined inside the exact fiber to
an exact network with a strictly zero neuron, and a component is reducible iff it contains
a network with `HasMergeableOrRedundantNeuron` (iff with `HasListedDegeneracy`).
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Padding.Strong

open BigOperators MaxCaterpillar.Fiber.Padding

variable {N h₁ h₂ : ℕ}

theorem relu_mul_nonneg {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : relu (c * t) = c * relu t := by
  rcases hc.eq_or_lt with h | h
  · subst h
    simp [relu]
  · exact Frontier.relu_mul_pos h t

/-! ## Weight-level degeneracies -/

/-- (a), first hidden layer: the incoming row and the bias of `j'` are `c ≥ 0` times those
of another neuron `j`. -/
def FirstProportional (net : Network N h₁ h₂) (j j' : Fin h₁) : Prop :=
  j ≠ j' ∧ ∃ c : ℝ, 0 ≤ c ∧ (∀ i, net.W₁ j' i = c * net.W₁ j i) ∧ net.b₁ j' = c * net.b₁ j

/-- (a), second hidden layer. -/
def SecondProportional (net : Network N h₁ h₂) (k k' : Fin h₂) : Prop :=
  k ≠ k' ∧ ∃ c : ℝ, 0 ≤ c ∧ (∀ j, net.W₂ k' j = c * net.W₂ k j) ∧ net.b₂ k' = c * net.b₂ k

/-- (b), first hidden layer: the neuron is active at no input. -/
def FirstNeverActive (net : Network N h₁ h₂) (j : Fin h₁) : Prop :=
  ∀ x : Point N, (∑ i, net.W₁ j i * x i) + net.b₁ j ≤ 0

/-- (b), second hidden layer: the neuron is active at no input, i.e. its preactivation is
nonpositive on the range of the first-layer features. -/
def SecondNeverActive (net : Network N h₁ h₂) (k : Fin h₂) : Prop :=
  ∀ x : Point N, pre₂ net k x ≤ 0

/-- (c): zero incoming weights, arbitrary bias. -/
def FirstZeroRow (net : Network N h₁ h₂) (j : Fin h₁) : Prop := ∀ i, net.W₁ j i = 0

/-- (d): the preactivation of the second-hidden-layer neuron is a constant function. -/
def SecondConstantPre (net : Network N h₁ h₂) (k : Fin h₂) : Prop :=
  ∃ c₀ : ℝ, ∀ x : Point N, pre₂ net k x = c₀

/-- Special case of (d): zero incoming weights, arbitrary bias. -/
def SecondZeroRow (net : Network N h₁ h₂) (k : Fin h₂) : Prop := ∀ j, net.W₂ k j = 0

/-- (e): two distinct second-hidden-layer neurons, both active at every input, whose output
weights do not have strictly opposite signs. -/
def SecondActiveSameSign (net : Network N h₁ h₂) (k k' : Fin h₂) : Prop :=
  k ≠ k' ∧ (∀ x, 0 ≤ pre₂ net k x) ∧ (∀ x, 0 ≤ pre₂ net k' x) ∧ 0 ≤ net.w₃ k * net.w₃ k'

/-! ## Weight-level degeneracies are semantic ones -/

theorem firstDependent_of_const {net : Network N h₁ h₂} {j : Fin h₁} {c₀ : ℝ}
    (h : ∀ x, act₁ net j x = c₀) : FirstDependent net j :=
  ⟨fun _ => 0, c₀, rfl, fun x => by simp [h x]⟩

theorem secondDependent_of_const {net : Network N h₁ h₂} {k : Fin h₂} {c₀ : ℝ}
    (h : ∀ x, act₂ net k x = c₀) : SecondDependent net k :=
  ⟨fun _ => 0, c₀, rfl, fun x => by simp [h x]⟩

theorem FirstProportional.firstDependent {net : Network N h₁ h₂} {j j' : Fin h₁}
    (h : FirstProportional net j j') : FirstDependent net j' := by
  obtain ⟨hne, c, hc, hW, hb⟩ := h
  refine ⟨fun i => if i = j then c else 0, 0, if_neg (Ne.symm hne), fun x => ?_⟩
  have hact : act₁ net j' x = c * act₁ net j x := by
    unfold act₁
    rw [← relu_mul_nonneg hc, hb, mul_add, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by rw [hW i]; ring
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero]
  exact hact

theorem SecondProportional.secondDependent {net : Network N h₁ h₂} {k k' : Fin h₂}
    (h : SecondProportional net k k') : SecondDependent net k' := by
  obtain ⟨hne, c, hc, hW, hb⟩ := h
  refine ⟨fun i => if i = k then c else 0, 0, if_neg (Ne.symm hne), fun x => ?_⟩
  have hact : act₂ net k' x = c * act₂ net k x := by
    unfold act₂ pre₂
    rw [← relu_mul_nonneg hc, hb, mul_add, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by rw [hW i]; ring
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero]
  exact hact

theorem FirstNeverActive.firstDependent {net : Network N h₁ h₂} {j : Fin h₁}
    (h : FirstNeverActive net j) : FirstDependent net j :=
  firstDependent_of_const (c₀ := 0) fun x => relu_of_nonpos (h x)

theorem SecondNeverActive.secondDependent {net : Network N h₁ h₂} {k : Fin h₂}
    (h : SecondNeverActive net k) : SecondDependent net k :=
  secondDependent_of_const (c₀ := 0) fun x => relu_of_nonpos (h x)

theorem FirstZeroRow.firstDependent {net : Network N h₁ h₂} {j : Fin h₁}
    (h : FirstZeroRow net j) : FirstDependent net j :=
  firstDependent_of_const (c₀ := relu (net.b₁ j)) fun x => by
    unfold act₁
    simp [show ∀ i, net.W₁ j i = 0 from h]

theorem SecondConstantPre.secondDependent {net : Network N h₁ h₂} {k : Fin h₂}
    (h : SecondConstantPre net k) : SecondDependent net k := by
  obtain ⟨c₀, hc⟩ := h
  exact secondDependent_of_const (c₀ := relu c₀) fun x => by
    unfold act₂
    rw [hc x]

theorem SecondZeroRow.secondConstantPre {net : Network N h₁ h₂} {k : Fin h₂}
    (h : SecondZeroRow net k) : SecondConstantPre net k :=
  ⟨net.b₂ k, fun x => by
    unfold pre₂
    simp [show ∀ j, net.W₂ k j = 0 from h]⟩

/-! ## The strong predicates -/

/-- The strong notion: some hidden neuron is removable, or its output function is an affine
combination of the output functions of the other neurons of its layer, or it is an
always-active second-hidden-layer neuron that another always-active neuron can absorb. -/
def HasMergeableOrRedundantNeuron (net : Network N h₁ h₂) : Prop :=
  HasRemovableNeuron net ∨ (∃ j, FirstDependent net j) ∨ (∃ k, SecondDependent net k) ∨
    ∃ k k', SecondActiveAbsorb net k k'

/-- The weight-level list (a)-(e). -/
def HasListedDegeneracy (net : Network N h₁ h₂) : Prop :=
  HasRemovableNeuron net ∨ (∃ j j', FirstProportional net j j') ∨
    (∃ k k', SecondProportional net k k') ∨ (∃ j, FirstNeverActive net j) ∨
    (∃ k, SecondNeverActive net k) ∨ (∃ j, FirstZeroRow net j) ∨
    (∃ k, SecondConstantPre net k) ∨ ∃ k k', SecondActiveSameSign net k k'

theorem SecondActiveSameSign.hasMergeableOrRedundantNeuron {net : Network N h₁ h₂}
    {k k' : Fin h₂} (h : SecondActiveSameSign net k k') :
    HasMergeableOrRedundantNeuron net := by
  obtain ⟨hne, hk, hk', hw⟩ := h
  by_cases h0 : net.w₃ k = 0
  · exact Or.inl (Or.inr ⟨k, Or.inl h0⟩)
  · refine Or.inr (Or.inr (Or.inr ⟨k, k', hne, hk, hk', net.w₃ k' / net.w₃ k, 0, ?_, ?_⟩))
    · field_simp
    · intro x
      have hs : 0 ≤ net.w₃ k' / net.w₃ k := by
        have : net.w₃ k' / net.w₃ k = (net.w₃ k * net.w₃ k') / (net.w₃ k) ^ 2 := by
          field_simp
          ring
        rw [this]
        exact div_nonneg hw (sq_nonneg _)
      have := mul_nonneg hs (hk' x)
      linarith [hk x]

theorem HasListedDegeneracy.hasMergeableOrRedundantNeuron {net : Network N h₁ h₂}
    (h : HasListedDegeneracy net) : HasMergeableOrRedundantNeuron net := by
  rcases h with h | ⟨j, j', h⟩ | ⟨k, k', h⟩ | ⟨j, h⟩ | ⟨k, h⟩ | ⟨j, h⟩ | ⟨k, h⟩ | ⟨k, k', h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨j', h.firstDependent⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨k', h.secondDependent⟩))
  · exact Or.inr (Or.inl ⟨j, h.firstDependent⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨k, h.secondDependent⟩))
  · exact Or.inr (Or.inl ⟨j, h.firstDependent⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨k, h.secondDependent⟩))
  · exact h.hasMergeableOrRedundantNeuron

theorem HasRemovableNeuron.hasListedDegeneracy {net : Network N h₁ h₂}
    (h : HasRemovableNeuron net) : HasListedDegeneracy net := Or.inl h

/-! ## Paths inside the exact fiber -/

section Fiber

variable [NeZero N]

theorem joined_outDead_of_firstDependent (net : ExactFiber N h₁ h₂) (j' : Fin h₁)
    (h : FirstDependent net.val j') :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧ FirstOutDead net'.val j' := by
  obtain ⟨c, c₀, hc, hrel⟩ := h
  let γ : ℝ → ExactFiber N h₁ h₂ := fun t =>
    ⟨transferFirst net.val j' c c₀ t,
      fun x => (transferFirst_eval net.val j' c c₀ t hrel x).trans (net.property x)⟩
  have hγ : Continuous γ := (continuous_transferFirst net.val j' c c₀).subtype_mk _
  have h0 : γ 0 = net := Subtype.ext (transferFirst_zero net.val j' c c₀)
  refine ⟨γ 1, ?_, transferFirst_one_outDead net.val j' c c₀ hc⟩
  have hj := joined_of_continuous_line hγ
  rw [h0] at hj
  exact hj.symm

theorem joined_outDead_of_secondDependent (net : ExactFiber N h₁ h₂) (k' : Fin h₂)
    (h : SecondDependent net.val k') :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧ SecondOutDead net'.val k' := by
  obtain ⟨c, c₀, hc, hrel⟩ := h
  let γ : ℝ → ExactFiber N h₁ h₂ := fun t =>
    ⟨transferSecond net.val k' c c₀ t,
      fun x => (transferSecond_eval net.val k' c c₀ t hrel x).trans (net.property x)⟩
  have hγ : Continuous γ := (continuous_transferSecond net.val k' c c₀).subtype_mk _
  have h0 : γ 0 = net := Subtype.ext (transferSecond_zero net.val k' c c₀)
  refine ⟨γ 1, ?_, transferSecond_one_outDead net.val k' c c₀ hc⟩
  have hj := joined_of_continuous_line hγ
  rw [h0] at hj
  exact hj.symm

theorem joined_outDead_of_secondActiveAbsorb (net : ExactFiber N h₁ h₂) (k k' : Fin h₂)
    (h : SecondActiveAbsorb net.val k k') :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧ SecondOutDead net'.val k' := by
  obtain ⟨hne, hk, hk', s, M, hw, hM⟩ := h
  let clamp : ℝ → ℝ := fun t => max 0 (min t 1)
  have hclamp : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
  have hc0 : ∀ t, 0 ≤ clamp t := fun t => le_max_left _ _
  have hc1 : ∀ t, clamp t ≤ 1 := fun t => max_le zero_le_one (min_le_right _ _)
  let γ : ℝ → ExactFiber N h₁ h₂ := fun t =>
    ⟨absorbSecond net.val k k' s M (clamp t),
      fun x => (absorbSecond_eval net.val k k' s M (clamp t) hne hk hk' hw hM (hc0 t) (hc1 t)
        x).trans (net.property x)⟩
  have hγ : Continuous γ :=
    ((continuous_absorbSecond net.val k k' s M).comp hclamp).subtype_mk _
  have e0 : clamp 0 = 0 := by simp
  have e1 : clamp 1 = 1 := by simp
  have h0 : γ 0 = net := Subtype.ext (by
    change absorbSecond net.val k k' s M (clamp 0) = net.val
    rw [e0, absorbSecond_zero])
  refine ⟨γ 1, ?_, ?_⟩
  · have hj := joined_of_continuous_line hγ
    rw [h0] at hj
    exact hj.symm
  · change SecondOutDead (absorbSecond net.val k k' s M (clamp 1)) k'
    rw [e1]
    exact absorbSecond_one_outDead net.val k k' s M

/-- **The user's conjecture, part 1.** An exact network with a mergeable or redundant hidden
neuron is joined, by a path inside the exact fiber, to an exact network with a removable
hidden neuron. -/
theorem exists_joined_hasRemovableNeuron (net : ExactFiber N h₁ h₂)
    (h : HasMergeableOrRedundantNeuron net.val) :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧ HasRemovableNeuron net'.val := by
  rcases h with h | ⟨j, h⟩ | ⟨k, h⟩ | ⟨k, k', h⟩
  · exact ⟨net, Joined.refl net, h⟩
  · obtain ⟨net', hj, hd⟩ := joined_outDead_of_firstDependent net j h
    exact ⟨net', hj, Or.inl ⟨j, Or.inl hd⟩⟩
  · obtain ⟨net', hj, hd⟩ := joined_outDead_of_secondDependent net k h
    exact ⟨net', hj, Or.inr ⟨k, Or.inl hd⟩⟩
  · obtain ⟨net', hj, hd⟩ := joined_outDead_of_secondActiveAbsorb net k k' h
    exact ⟨net', hj, Or.inr ⟨k', Or.inl hd⟩⟩

/-- **The user's conjecture.** An exact network with a mergeable or redundant hidden neuron
is joined, by a path inside the exact fiber, to an exact network having a hidden neuron with
zero incoming weights, zero bias and zero outgoing weights. -/
theorem exists_joined_hasZeroNeuron_of_mergeableOrRedundant (net : ExactFiber N h₁ h₂)
    (h : HasMergeableOrRedundantNeuron net.val) :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧ HasZeroNeuron net'.val := by
  obtain ⟨net₁, hj₁, hrem⟩ := exists_joined_hasRemovableNeuron net h
  obtain ⟨net₂, hj₂, hzero⟩ := exists_joined_hasZeroNeuron net₁ hrem
  exact ⟨net₂, hj₁.trans hj₂, hzero⟩

/-- The same for the weight-level list (a)-(e). -/
theorem exists_joined_hasZeroNeuron_of_listedDegeneracy (net : ExactFiber N h₁ h₂)
    (h : HasListedDegeneracy net.val) :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧ HasZeroNeuron net'.val :=
  exists_joined_hasZeroNeuron_of_mergeableOrRedundant net h.hasMergeableOrRedundantNeuron

/-! ## Reducible components under the strong notion -/

/-- A component of the symmetry quotient is reducible iff it contains (the class of) an
exact network with a mergeable or redundant hidden neuron. -/
theorem isReducibleComponent_iff_mergeableOrRedundant
    (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂,
      HasMergeableOrRedundantNeuron net.val ∧
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C := by
  constructor
  · rintro ⟨net, hrem, hC⟩
    exact ⟨net, Or.inl hrem, hC⟩
  · rintro ⟨net, h, rfl⟩
    obtain ⟨net', hjoin, hrem⟩ := exists_joined_hasRemovableNeuron net h
    exact ⟨net', hrem, (quotient_component_eq_of_joined hjoin).symm⟩

/-- The same with the weight-level list (a)-(e). -/
theorem isReducibleComponent_iff_listedDegeneracy
    (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasListedDegeneracy net.val ∧
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C := by
  constructor
  · rintro ⟨net, hrem, hC⟩
    exact ⟨net, Or.inl hrem, hC⟩
  · rintro ⟨net, h, hC⟩
    exact (isReducibleComponent_iff_mergeableOrRedundant C).mpr
      ⟨net, h.hasMergeableOrRedundantNeuron, hC⟩

/-- Raw-fiber version (components of the exact fiber before the symmetry quotient). -/
theorem isReducibleRawComponent_iff_mergeableOrRedundant
    (C : ConnectedComponents (ExactFiber N h₁ h₂)) :
    IsReducibleRawComponent C ↔ ∃ net : ExactFiber N h₁ h₂,
      HasMergeableOrRedundantNeuron net.val ∧
      (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C := by
  constructor
  · rintro ⟨net, hrem, hC⟩
    exact ⟨net, Or.inl hrem, hC⟩
  · rintro ⟨net, h, rfl⟩
    obtain ⟨net', hjoin, hrem⟩ := exists_joined_hasRemovableNeuron net h
    exact ⟨net', hrem, (component_eq_of_joined hjoin).symm⟩

theorem isReducibleRawComponent_iff_listedDegeneracy
    (C : ConnectedComponents (ExactFiber N h₁ h₂)) :
    IsReducibleRawComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasListedDegeneracy net.val ∧
      (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C := by
  constructor
  · rintro ⟨net, hrem, hC⟩
    exact ⟨net, Or.inl hrem, hC⟩
  · rintro ⟨net, h, hC⟩
    exact (isReducibleRawComponent_iff_mergeableOrRedundant C).mpr
      ⟨net, h.hasMergeableOrRedundantNeuron, hC⟩

end Fiber

end MaxCaterpillar.Fiber.Padding.Strong
