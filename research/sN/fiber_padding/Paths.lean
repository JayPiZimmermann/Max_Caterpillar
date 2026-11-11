import research.sN.fiber_padding.Defs

/-! # Reducible components, and independence of the padding convention

`IsReducibleComponent C` (for a connected component `C` of the symmetry quotient of the
exact fiber) and `IsReducibleRawComponent C` (for a connected component of the exact fiber
itself) say that `C` contains (the class of) an exact network having a removable hidden
neuron.

The two padding conventions give the same reducible components:

* a neuron with zero outgoing weights can have its incoming weights and its bias scaled
  to zero along a path inside the exact fiber (`scaleFirstIn`, `scaleSecondIn`);
* a neuron with zero incoming weights and zero bias can have its outgoing weights scaled
  to zero along a path inside the exact fiber (`scaleFirstOut`, `scaleSecondOut`).

Hence every exact network with a removable neuron is joined, inside the exact fiber, to an
exact network with a strictly zero neuron (`exists_joined_hasZeroNeuron`), and
`isReducibleComponent_iff_outDead`, `isReducibleComponent_iff_inDead`,
`isReducibleComponent_iff_zeroNeuron`, `isReducibleComponent_iff_padded` are all
characterizations of the same notion.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Padding

open BigOperators

variable {N h₁ h₂ : ℕ}

/-! ## Elementary topology -/

theorem component_eq_of_joined {X : Type*} [TopologicalSpace X] {x y : X} (h : Joined x y) :
    (x : ConnectedComponents X) = y :=
  ConnectedComponents.coe_eq_coe'.mpr (pathComponent_subset_component y h.symm)

/-- A continuous real one-parameter family joins its values at `1` and at `0`. -/
theorem joined_of_continuous_line {X : Type*} [TopologicalSpace X] {γ : ℝ → X}
    (hγ : Continuous γ) : Joined (γ 1) (γ 0) :=
  ⟨{ toFun := fun t => γ (1 - (t : ℝ))
     continuous_toFun := hγ.comp (continuous_const.sub continuous_subtype_val)
     source' := by simp
     target' := by simp }⟩

/-! ## The four scaling moves -/

/-- The multiplier equal to `c` at index `j` and to `1` at every other index. -/
def mult {n : ℕ} (j : Fin n) (c : ℝ) (j' : Fin n) : ℝ := if j' = j then c else 1

@[simp] theorem mult_self {n : ℕ} (j : Fin n) (c : ℝ) : mult j c j = c := if_pos rfl

theorem mult_of_ne {n : ℕ} {j j' : Fin n} (h : j' ≠ j) (c : ℝ) : mult j c j' = 1 := if_neg h

@[simp] theorem mult_one {n : ℕ} (j j' : Fin n) : mult j 1 j' = 1 := by
  unfold mult
  split_ifs <;> rfl

theorem continuous_mult {n : ℕ} (j j' : Fin n) : Continuous (fun c : ℝ => mult j c j') := by
  unfold mult
  split_ifs
  · exact continuous_id
  · exact continuous_const

/-- Multiply the incoming weights and the bias of first-hidden-layer neuron `j` by `c`. -/
def scaleFirstIn (net : Network N h₁ h₂) (j : Fin h₁) (c : ℝ) : Network N h₁ h₂ where
  W₁ j' i := mult j c j' * net.W₁ j' i
  b₁ j' := mult j c j' * net.b₁ j'
  W₂ := net.W₂
  b₂ := net.b₂
  w₃ := net.w₃
  b₃ := net.b₃

/-- Multiply the outgoing weights of first-hidden-layer neuron `j` by `c`. -/
def scaleFirstOut (net : Network N h₁ h₂) (j : Fin h₁) (c : ℝ) : Network N h₁ h₂ where
  W₁ := net.W₁
  b₁ := net.b₁
  W₂ k j' := mult j c j' * net.W₂ k j'
  b₂ := net.b₂
  w₃ := net.w₃
  b₃ := net.b₃

/-- Multiply the incoming weights and the bias of second-hidden-layer neuron `k` by `c`. -/
def scaleSecondIn (net : Network N h₁ h₂) (k : Fin h₂) (c : ℝ) : Network N h₁ h₂ where
  W₁ := net.W₁
  b₁ := net.b₁
  W₂ k' j := mult k c k' * net.W₂ k' j
  b₂ k' := mult k c k' * net.b₂ k'
  w₃ := net.w₃
  b₃ := net.b₃

/-- Multiply the outgoing weight of second-hidden-layer neuron `k` by `c`. -/
def scaleSecondOut (net : Network N h₁ h₂) (k : Fin h₂) (c : ℝ) : Network N h₁ h₂ where
  W₁ := net.W₁
  b₁ := net.b₁
  W₂ := net.W₂
  b₂ := net.b₂
  w₃ k' := mult k c k' * net.w₃ k'
  b₃ := net.b₃

theorem scaleFirstIn_eval (net : Network N h₁ h₂) (j : Fin h₁) (h : FirstOutDead net j)
    (c : ℝ) (x : Point N) : (scaleFirstIn net j c).eval x = net.eval x := by
  unfold Network.eval scaleFirstIn
  apply congrArg (fun z => z + net.b₃)
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun z => net.w₃ k * relu (z + net.b₂ k))
  apply Finset.sum_congr rfl
  intro j' _
  by_cases hj : j' = j
  · subst hj
    rw [h k, zero_mul, zero_mul]
  · simp only [mult_of_ne hj, one_mul]

theorem scaleFirstOut_eval (net : Network N h₁ h₂) (j : Fin h₁) (h : FirstInDead net j)
    (c : ℝ) (x : Point N) : (scaleFirstOut net j c).eval x = net.eval x := by
  unfold Network.eval scaleFirstOut
  apply congrArg (fun z => z + net.b₃)
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun z => net.w₃ k * relu (z + net.b₂ k))
  apply Finset.sum_congr rfl
  intro j' _
  by_cases hj : j' = j
  · subst hj
    rw [h.activation_eq_zero x, mul_zero, mul_zero]
  · simp only [mult_of_ne hj, one_mul]

theorem scaleSecondIn_eval (net : Network N h₁ h₂) (k : Fin h₂) (h : SecondOutDead net k)
    (c : ℝ) (x : Point N) : (scaleSecondIn net k c).eval x = net.eval x := by
  unfold Network.eval scaleSecondIn
  apply congrArg (fun z => z + net.b₃)
  apply Finset.sum_congr rfl
  intro k' _
  by_cases hk : k' = k
  · subst hk
    rw [show net.w₃ k' = 0 from h, zero_mul, zero_mul]
  · simp only [mult_of_ne hk, one_mul]

theorem scaleSecondOut_eval (net : Network N h₁ h₂) (k : Fin h₂) (h : SecondInDead net k)
    (c : ℝ) (x : Point N) : (scaleSecondOut net k c).eval x = net.eval x := by
  unfold Network.eval scaleSecondOut
  apply congrArg (fun z => z + net.b₃)
  apply Finset.sum_congr rfl
  intro k' _
  by_cases hk : k' = k
  · subst hk
    rw [h.activation_eq_zero x, mul_zero, mul_zero]
  · simp only [mult_of_ne hk, one_mul]

theorem scaleFirstIn_one (net : Network N h₁ h₂) (j : Fin h₁) : scaleFirstIn net j 1 = net := by
  cases net
  simp [scaleFirstIn]

theorem scaleFirstOut_one (net : Network N h₁ h₂) (j : Fin h₁) :
    scaleFirstOut net j 1 = net := by
  cases net
  simp [scaleFirstOut]

theorem scaleSecondIn_one (net : Network N h₁ h₂) (k : Fin h₂) :
    scaleSecondIn net k 1 = net := by
  cases net
  simp [scaleSecondIn]

theorem scaleSecondOut_one (net : Network N h₁ h₂) (k : Fin h₂) :
    scaleSecondOut net k 1 = net := by
  cases net
  simp [scaleSecondOut]

theorem continuous_scaleFirstIn (net : Network N h₁ h₂) (j : Fin h₁) :
    Continuous (fun c : ℝ => scaleFirstIn net j c) := by
  apply (continuous_network_iff _).2
  refine ⟨?_, ?_, continuous_const, continuous_const, continuous_const, continuous_const⟩
  · exact continuous_pi fun j' => continuous_pi fun i =>
      (continuous_mult j j').mul continuous_const
  · exact continuous_pi fun j' => (continuous_mult j j').mul continuous_const

theorem continuous_scaleFirstOut (net : Network N h₁ h₂) (j : Fin h₁) :
    Continuous (fun c : ℝ => scaleFirstOut net j c) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, ?_, continuous_const, continuous_const,
    continuous_const⟩
  exact continuous_pi fun k => continuous_pi fun j' =>
    (continuous_mult j j').mul continuous_const

theorem continuous_scaleSecondIn (net : Network N h₁ h₂) (k : Fin h₂) :
    Continuous (fun c : ℝ => scaleSecondIn net k c) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, ?_, ?_, continuous_const, continuous_const⟩
  · exact continuous_pi fun k' => continuous_pi fun j =>
      (continuous_mult k k').mul continuous_const
  · exact continuous_pi fun k' => (continuous_mult k k').mul continuous_const

theorem continuous_scaleSecondOut (net : Network N h₁ h₂) (k : Fin h₂) :
    Continuous (fun c : ℝ => scaleSecondOut net k c) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, continuous_const, continuous_const, ?_,
    continuous_const⟩
  exact continuous_pi fun k' => (continuous_mult k k').mul continuous_const

/-! ## Every removable neuron can be turned into a zero neuron inside the exact fiber -/

section Fiber

variable [NeZero N]

theorem joined_zero_of_firstOutDead (net : ExactFiber N h₁ h₂) (j : Fin h₁)
    (h : FirstOutDead net.val j) :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧
      FirstOutDead net'.val j ∧ FirstInDead net'.val j := by
  let γ : ℝ → ExactFiber N h₁ h₂ := fun c =>
    ⟨scaleFirstIn net.val j c, fun x => (scaleFirstIn_eval net.val j h c x).trans (net.property x)⟩
  have hγ : Continuous γ := (continuous_scaleFirstIn net.val j).subtype_mk _
  have h1 : γ 1 = net := Subtype.ext (scaleFirstIn_one net.val j)
  refine ⟨γ 0, ?_, h, ?_⟩
  · have hj := joined_of_continuous_line hγ
    rwa [h1] at hj
  · refine ⟨fun i => ?_, ?_⟩
    · change mult j 0 j * net.val.W₁ j i = 0
      rw [mult_self, zero_mul]
    · change mult j 0 j * net.val.b₁ j = 0
      rw [mult_self, zero_mul]

theorem joined_zero_of_firstInDead (net : ExactFiber N h₁ h₂) (j : Fin h₁)
    (h : FirstInDead net.val j) :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧
      FirstOutDead net'.val j ∧ FirstInDead net'.val j := by
  let γ : ℝ → ExactFiber N h₁ h₂ := fun c =>
    ⟨scaleFirstOut net.val j c,
      fun x => (scaleFirstOut_eval net.val j h c x).trans (net.property x)⟩
  have hγ : Continuous γ := (continuous_scaleFirstOut net.val j).subtype_mk _
  have h1 : γ 1 = net := Subtype.ext (scaleFirstOut_one net.val j)
  refine ⟨γ 0, ?_, ?_, h⟩
  · have hj := joined_of_continuous_line hγ
    rwa [h1] at hj
  · intro k
    change mult j 0 j * net.val.W₂ k j = 0
    rw [mult_self, zero_mul]

theorem joined_zero_of_secondOutDead (net : ExactFiber N h₁ h₂) (k : Fin h₂)
    (h : SecondOutDead net.val k) :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧
      SecondOutDead net'.val k ∧ SecondInDead net'.val k := by
  let γ : ℝ → ExactFiber N h₁ h₂ := fun c =>
    ⟨scaleSecondIn net.val k c,
      fun x => (scaleSecondIn_eval net.val k h c x).trans (net.property x)⟩
  have hγ : Continuous γ := (continuous_scaleSecondIn net.val k).subtype_mk _
  have h1 : γ 1 = net := Subtype.ext (scaleSecondIn_one net.val k)
  refine ⟨γ 0, ?_, h, ?_⟩
  · have hj := joined_of_continuous_line hγ
    rwa [h1] at hj
  · refine ⟨fun j => ?_, ?_⟩
    · change mult k 0 k * net.val.W₂ k j = 0
      rw [mult_self, zero_mul]
    · change mult k 0 k * net.val.b₂ k = 0
      rw [mult_self, zero_mul]

theorem joined_zero_of_secondInDead (net : ExactFiber N h₁ h₂) (k : Fin h₂)
    (h : SecondInDead net.val k) :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧
      SecondOutDead net'.val k ∧ SecondInDead net'.val k := by
  let γ : ℝ → ExactFiber N h₁ h₂ := fun c =>
    ⟨scaleSecondOut net.val k c,
      fun x => (scaleSecondOut_eval net.val k h c x).trans (net.property x)⟩
  have hγ : Continuous γ := (continuous_scaleSecondOut net.val k).subtype_mk _
  have h1 : γ 1 = net := Subtype.ext (scaleSecondOut_one net.val k)
  refine ⟨γ 0, ?_, ?_, h⟩
  · have hj := joined_of_continuous_line hγ
    rwa [h1] at hj
  · change mult k 0 k * net.val.w₃ k = 0
    rw [mult_self, zero_mul]

/-- **Independence of the convention.** Every exact network with a removable hidden neuron
(under either convention) is joined, by a path inside the exact fiber, to an exact network
in which that neuron has zero incoming weights, zero bias and zero outgoing weights. -/
theorem exists_joined_hasZeroNeuron (net : ExactFiber N h₁ h₂)
    (h : HasRemovableNeuron net.val) :
    ∃ net' : ExactFiber N h₁ h₂, Joined net net' ∧ HasZeroNeuron net'.val := by
  rcases h with ⟨j, hj | hj⟩ | ⟨k, hk | hk⟩
  · obtain ⟨net', hjoin, ho, hi⟩ := joined_zero_of_firstOutDead net j hj
    exact ⟨net', hjoin, Or.inl ⟨j, ho, hi⟩⟩
  · obtain ⟨net', hjoin, ho, hi⟩ := joined_zero_of_firstInDead net j hj
    exact ⟨net', hjoin, Or.inl ⟨j, ho, hi⟩⟩
  · obtain ⟨net', hjoin, ho, hi⟩ := joined_zero_of_secondOutDead net k hk
    exact ⟨net', hjoin, Or.inr ⟨k, ho, hi⟩⟩
  · obtain ⟨net', hjoin, ho, hi⟩ := joined_zero_of_secondInDead net k hk
    exact ⟨net', hjoin, Or.inr ⟨k, ho, hi⟩⟩

/-- Points joined inside the exact fiber have the same component in the symmetry quotient. -/
theorem quotient_component_eq_of_joined {a b : ExactFiber N h₁ h₂} (h : Joined a b) :
    ((quotientMk a : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = quotientMk b :=
  component_eq_of_joined ⟨h.somePath.map quotientMk_continuous⟩

/-! ## Reducible components -/

/-- A connected component of the symmetry quotient of the exact fiber is *reducible* if it
contains the class of an exact network having a removable hidden neuron. By
`isReducibleComponent_iff_padded` this is the same as: the component meets the padded image
of the exact fiber of a strictly smaller architecture. -/
def IsReducibleComponent (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) : Prop :=
  ∃ net : ExactFiber N h₁ h₂, HasRemovableNeuron net.val ∧
    ((quotientMk net : SymmetryQuotient N h₁ h₂) :
      ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C

/-- The same notion for a connected component of the exact fiber before any quotient. -/
def IsReducibleRawComponent (C : ConnectedComponents (ExactFiber N h₁ h₂)) : Prop :=
  ∃ net : ExactFiber N h₁ h₂, HasRemovableNeuron net.val ∧
    (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C

/-- Reducibility in terms of strict zero padding. -/
theorem isReducibleComponent_iff_zeroNeuron
    (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasZeroNeuron net.val ∧
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C := by
  constructor
  · rintro ⟨net, hrem, rfl⟩
    obtain ⟨net', hjoin, hzero⟩ := exists_joined_hasZeroNeuron net hrem
    exact ⟨net', hzero, (quotient_component_eq_of_joined hjoin).symm⟩
  · rintro ⟨net, hzero, rfl⟩
    exact ⟨net, hzero.hasRemovableNeuron, rfl⟩

/-- Reducibility in terms of convention A (zero outgoing weights). -/
theorem isReducibleComponent_iff_outDead
    (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasOutDeadNeuron net.val ∧
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C := by
  constructor
  · intro h
    obtain ⟨net, hzero, hC⟩ := (isReducibleComponent_iff_zeroNeuron C).mp h
    exact ⟨net, hzero.hasOutDeadNeuron, hC⟩
  · rintro ⟨net, hout, rfl⟩
    exact ⟨net, hout.hasRemovableNeuron, rfl⟩

/-- Reducibility in terms of convention B (zero incoming weights and zero bias). -/
theorem isReducibleComponent_iff_inDead
    (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasInDeadNeuron net.val ∧
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C := by
  constructor
  · intro h
    obtain ⟨net, hzero, hC⟩ := (isReducibleComponent_iff_zeroNeuron C).mp h
    exact ⟨net, hzero.hasInDeadNeuron, hC⟩
  · rintro ⟨net, hin, rfl⟩
    exact ⟨net, hin.hasRemovableNeuron, rfl⟩

/-- Reducibility in terms of padded solutions of strictly smaller architectures. -/
theorem isReducibleComponent_iff_padded
    (C : ConnectedComponents (SymmetryQuotient N h₁ h₂)) :
    IsReducibleComponent C ↔ ∃ net : ExactFiber N h₁ h₂, IsPaddedSolution net.val ∧
      ((quotientMk net : SymmetryQuotient N h₁ h₂) :
        ConnectedComponents (SymmetryQuotient N h₁ h₂)) = C := by
  constructor
  · rintro ⟨net, hrem, hC⟩
    exact ⟨net, (isPaddedSolution_iff net.val).mpr ⟨net.property, hrem⟩, hC⟩
  · rintro ⟨net, hpad, hC⟩
    exact ⟨net, ((isPaddedSolution_iff net.val).mp hpad).2, hC⟩

theorem isReducibleRawComponent_iff_zeroNeuron
    (C : ConnectedComponents (ExactFiber N h₁ h₂)) :
    IsReducibleRawComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasZeroNeuron net.val ∧
      (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C := by
  constructor
  · rintro ⟨net, hrem, rfl⟩
    obtain ⟨net', hjoin, hzero⟩ := exists_joined_hasZeroNeuron net hrem
    exact ⟨net', hzero, (component_eq_of_joined hjoin).symm⟩
  · rintro ⟨net, hzero, rfl⟩
    exact ⟨net, hzero.hasRemovableNeuron, rfl⟩

theorem isReducibleRawComponent_iff_outDead
    (C : ConnectedComponents (ExactFiber N h₁ h₂)) :
    IsReducibleRawComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasOutDeadNeuron net.val ∧
      (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C := by
  constructor
  · intro h
    obtain ⟨net, hzero, hC⟩ := (isReducibleRawComponent_iff_zeroNeuron C).mp h
    exact ⟨net, hzero.hasOutDeadNeuron, hC⟩
  · rintro ⟨net, hout, rfl⟩
    exact ⟨net, hout.hasRemovableNeuron, rfl⟩

theorem isReducibleRawComponent_iff_inDead
    (C : ConnectedComponents (ExactFiber N h₁ h₂)) :
    IsReducibleRawComponent C ↔ ∃ net : ExactFiber N h₁ h₂, HasInDeadNeuron net.val ∧
      (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C := by
  constructor
  · intro h
    obtain ⟨net, hzero, hC⟩ := (isReducibleRawComponent_iff_zeroNeuron C).mp h
    exact ⟨net, hzero.hasInDeadNeuron, hC⟩
  · rintro ⟨net, hin, rfl⟩
    exact ⟨net, hin.hasRemovableNeuron, rfl⟩

theorem isReducibleRawComponent_iff_padded
    (C : ConnectedComponents (ExactFiber N h₁ h₂)) :
    IsReducibleRawComponent C ↔ ∃ net : ExactFiber N h₁ h₂, IsPaddedSolution net.val ∧
      (net : ConnectedComponents (ExactFiber N h₁ h₂)) = C := by
  constructor
  · rintro ⟨net, hrem, hC⟩
    exact ⟨net, (isPaddedSolution_iff net.val).mpr ⟨net.property, hrem⟩, hC⟩
  · rintro ⟨net, hpad, hC⟩
    exact ⟨net, ((isPaddedSolution_iff net.val).mp hpad).2, hC⟩

/-- The image in the symmetry quotient of a reducible component of the exact fiber is
contained in a reducible component of the quotient. -/
theorem IsReducibleRawComponent.quotient {C : ConnectedComponents (ExactFiber N h₁ h₂)}
    (h : IsReducibleRawComponent C) :
    IsReducibleComponent (quotientMk_continuous.connectedComponentsMap C) := by
  obtain ⟨net, hrem, rfl⟩ := h
  exact ⟨net, hrem, rfl⟩

end Fiber

end MaxCaterpillar.Fiber.Padding
