import MaxCaterpillar.Fiber.Symmetry
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.UnitInterval

/-! # Removable hidden neurons, padded solutions and reducible components

Everything here is stated for the ordinary model `Network N h₁ h₂` (arbitrary real
weights and biases, two hidden layers, no skip connections) and for arbitrary
`N h₁ h₂`.

## Neuron-level predicates

For a first-hidden-layer neuron `j` and a second-hidden-layer neuron `k`:

* `FirstOutDead net j`  : every outgoing weight `W₂ k j` vanishes (incoming row and bias arbitrary);
* `FirstInDead net j`   : the incoming row `W₁ j` and the bias `b₁ j` vanish (outgoing weights arbitrary);
* `SecondOutDead net k` : the outgoing weight `w₃ k` vanishes (incoming row and bias arbitrary);
* `SecondInDead net k`  : the incoming row `W₂ k` and the bias `b₂ k` vanish (outgoing weight arbitrary).

Convention A ("zero outgoing weights") is `HasOutDeadNeuron`, convention B ("zero incoming
weights and bias") is `HasInDeadNeuron`, their disjunction is `HasRemovableNeuron`, and the
strict zero padding (both at the same neuron) is `HasZeroNeuron`.

## Padding

`IsPaddingOf big small e₁ e₂` says that `small` sits inside `big` along injections of the
hidden neurons and every additional hidden neuron of `big` is removable.  Paddings compute the
same function (`IsPaddingOf.eval_eq`).  `IsPaddedSolution big` says that `big` is a padding of
an exact network of a strictly smaller architecture; `isPaddedSolution_iff` proves that this is
the same as: `big` is exact and has a removable hidden neuron.

## Symmetries

`DeadTransport a b` records relabelings of the hidden neurons under which the four
predicates of `b` are those of `a`; every allowed symmetry (positive rescaling, hidden and
input permutations) gives such a transport (`deadTransport_of_symmetry`), so all notions
descend to the symmetry quotient.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Padding

open BigOperators

variable {N h₁ h₂ : ℕ}

/-! ## Neuron-level predicates -/

/-- Convention A, first hidden layer: all outgoing weights of neuron `j` vanish.
The incoming weights and the bias of the neuron are arbitrary. -/
def FirstOutDead (net : Network N h₁ h₂) (j : Fin h₁) : Prop := ∀ k, net.W₂ k j = 0

/-- Convention B, first hidden layer: all incoming weights and the bias of neuron `j`
vanish. Its outgoing weights are arbitrary. -/
def FirstInDead (net : Network N h₁ h₂) (j : Fin h₁) : Prop :=
  (∀ i, net.W₁ j i = 0) ∧ net.b₁ j = 0

/-- Convention A, second hidden layer: the outgoing weight of neuron `k` vanishes.
The incoming weights and the bias of the neuron are arbitrary. -/
def SecondOutDead (net : Network N h₁ h₂) (k : Fin h₂) : Prop := net.w₃ k = 0

/-- Convention B, second hidden layer: all incoming weights and the bias of neuron `k`
vanish. Its outgoing weight is arbitrary. -/
def SecondInDead (net : Network N h₁ h₂) (k : Fin h₂) : Prop :=
  (∀ j, net.W₂ k j = 0) ∧ net.b₂ k = 0

/-- A first-hidden-layer neuron that is removable under either convention. -/
def FirstRemovable (net : Network N h₁ h₂) (j : Fin h₁) : Prop :=
  FirstOutDead net j ∨ FirstInDead net j

/-- A second-hidden-layer neuron that is removable under either convention. -/
def SecondRemovable (net : Network N h₁ h₂) (k : Fin h₂) : Prop :=
  SecondOutDead net k ∨ SecondInDead net k

/-- Convention A: some hidden neuron has zero outgoing weights. -/
def HasOutDeadNeuron (net : Network N h₁ h₂) : Prop :=
  (∃ j, FirstOutDead net j) ∨ ∃ k, SecondOutDead net k

/-- Convention B: some hidden neuron has zero incoming weights and zero bias. -/
def HasInDeadNeuron (net : Network N h₁ h₂) : Prop :=
  (∃ j, FirstInDead net j) ∨ ∃ k, SecondInDead net k

/-- Some hidden neuron is removable under convention A or under convention B. -/
def HasRemovableNeuron (net : Network N h₁ h₂) : Prop :=
  (∃ j, FirstRemovable net j) ∨ ∃ k, SecondRemovable net k

/-- Strict zero padding: some hidden neuron has zero incoming weights, zero bias and
zero outgoing weights. -/
def HasZeroNeuron (net : Network N h₁ h₂) : Prop :=
  (∃ j, FirstOutDead net j ∧ FirstInDead net j) ∨ ∃ k, SecondOutDead net k ∧ SecondInDead net k

theorem hasRemovableNeuron_iff (net : Network N h₁ h₂) :
    HasRemovableNeuron net ↔ HasOutDeadNeuron net ∨ HasInDeadNeuron net := by
  unfold HasRemovableNeuron HasOutDeadNeuron HasInDeadNeuron FirstRemovable SecondRemovable
  constructor
  · rintro (⟨j, hj | hj⟩ | ⟨k, hk | hk⟩)
    · exact Or.inl (Or.inl ⟨j, hj⟩)
    · exact Or.inr (Or.inl ⟨j, hj⟩)
    · exact Or.inl (Or.inr ⟨k, hk⟩)
    · exact Or.inr (Or.inr ⟨k, hk⟩)
  · rintro ((⟨j, hj⟩ | ⟨k, hk⟩) | (⟨j, hj⟩ | ⟨k, hk⟩))
    · exact Or.inl ⟨j, Or.inl hj⟩
    · exact Or.inr ⟨k, Or.inl hk⟩
    · exact Or.inl ⟨j, Or.inr hj⟩
    · exact Or.inr ⟨k, Or.inr hk⟩

theorem HasOutDeadNeuron.hasRemovableNeuron {net : Network N h₁ h₂}
    (h : HasOutDeadNeuron net) : HasRemovableNeuron net :=
  (hasRemovableNeuron_iff net).mpr (Or.inl h)

theorem HasInDeadNeuron.hasRemovableNeuron {net : Network N h₁ h₂}
    (h : HasInDeadNeuron net) : HasRemovableNeuron net :=
  (hasRemovableNeuron_iff net).mpr (Or.inr h)

theorem HasZeroNeuron.hasOutDeadNeuron {net : Network N h₁ h₂}
    (h : HasZeroNeuron net) : HasOutDeadNeuron net := by
  rcases h with ⟨j, hj, _⟩ | ⟨k, hk, _⟩
  · exact Or.inl ⟨j, hj⟩
  · exact Or.inr ⟨k, hk⟩

theorem HasZeroNeuron.hasInDeadNeuron {net : Network N h₁ h₂}
    (h : HasZeroNeuron net) : HasInDeadNeuron net := by
  rcases h with ⟨j, _, hj⟩ | ⟨k, _, hk⟩
  · exact Or.inl ⟨j, hj⟩
  · exact Or.inr ⟨k, hk⟩

theorem HasZeroNeuron.hasRemovableNeuron {net : Network N h₁ h₂}
    (h : HasZeroNeuron net) : HasRemovableNeuron net :=
  h.hasOutDeadNeuron.hasRemovableNeuron

/-- The activation of a first-hidden-layer neuron with zero incoming weights and zero
bias vanishes at every input. -/
theorem FirstInDead.activation_eq_zero {net : Network N h₁ h₂} {j : Fin h₁}
    (h : FirstInDead net j) (x : Point N) :
    relu ((∑ i, net.W₁ j i * x i) + net.b₁ j) = 0 := by
  simp [h.1, h.2, relu]

/-- The activation of a second-hidden-layer neuron with zero incoming weights and zero
bias vanishes at every input. -/
theorem SecondInDead.activation_eq_zero {net : Network N h₁ h₂} {k : Fin h₂}
    (h : SecondInDead net k) (x : Point N) :
    relu ((∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k) = 0 := by
  simp [h.1, h.2, relu]

/-! ## Deleting one hidden neuron -/

/-- Delete first-hidden-layer neuron `j`, together with its incoming row, its bias and
its outgoing column. No other parameter changes. -/
def removeFirst (net : Network N (h₁ + 1) h₂) (j : Fin (h₁ + 1)) : Network N h₁ h₂ where
  W₁ j' := net.W₁ (j.succAbove j')
  b₁ j' := net.b₁ (j.succAbove j')
  W₂ k j' := net.W₂ k (j.succAbove j')
  b₂ := net.b₂
  w₃ := net.w₃
  b₃ := net.b₃

/-- Delete second-hidden-layer neuron `k`, together with its incoming row, its bias and
its outgoing weight. No other parameter changes. -/
def removeSecond (net : Network N h₁ (h₂ + 1)) (k : Fin (h₂ + 1)) : Network N h₁ h₂ where
  W₁ := net.W₁
  b₁ := net.b₁
  W₂ k' := net.W₂ (k.succAbove k')
  b₂ k' := net.b₂ (k.succAbove k')
  w₃ k' := net.w₃ (k.succAbove k')
  b₃ := net.b₃

/-- Deleting a removable first-hidden-layer neuron does not change the function. -/
theorem removeFirst_eval (net : Network N (h₁ + 1) h₂) (j : Fin (h₁ + 1))
    (h : FirstRemovable net j) (x : Point N) :
    (removeFirst net j).eval x = net.eval x := by
  unfold Network.eval removeFirst
  dsimp only
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsplit := Fin.sum_univ_succAbove
    (fun j' => net.W₂ k j' * relu ((∑ i, net.W₁ j' i * x i) + net.b₁ j')) j
  have hz : net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j) = 0 := by
    rcases h with h | h
    · rw [h k, zero_mul]
    · rw [h.activation_eq_zero x, mul_zero]
  rw [hsplit, hz, zero_add]

/-- Deleting a removable second-hidden-layer neuron does not change the function. -/
theorem removeSecond_eval (net : Network N h₁ (h₂ + 1)) (k : Fin (h₂ + 1))
    (h : SecondRemovable net k) (x : Point N) :
    (removeSecond net k).eval x = net.eval x := by
  unfold Network.eval removeSecond
  dsimp only
  congr 1
  have hsplit := Fin.sum_univ_succAbove
    (fun k' => net.w₃ k' * relu ((∑ j, net.W₂ k' j *
      relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k')) k
  have hz : net.w₃ k * relu ((∑ j, net.W₂ k j *
      relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k) = 0 := by
    rcases h with h | h
    · rw [show net.w₃ k = 0 from h, zero_mul]
    · rw [h.activation_eq_zero x, mul_zero]
  rw [hsplit, hz, zero_add]

/-! ## General paddings along injections of hidden neurons -/

/-- `big` is a padding of `small`: the hidden neurons of `small` are embedded injectively
into those of `big`, all parameters among embedded neurons agree, and every additional
hidden neuron of `big` is removable (zero outgoing weights, or zero incoming weights and
zero bias). The remaining parameters attached to additional neurons are unrestricted. -/
structure IsPaddingOf {H₁ H₂ : ℕ} (big : Network N H₁ H₂) (small : Network N h₁ h₂)
    (e₁ : Fin h₁ ↪ Fin H₁) (e₂ : Fin h₂ ↪ Fin H₂) : Prop where
  W₁ : ∀ j i, big.W₁ (e₁ j) i = small.W₁ j i
  b₁ : ∀ j, big.b₁ (e₁ j) = small.b₁ j
  W₂ : ∀ k j, big.W₂ (e₂ k) (e₁ j) = small.W₂ k j
  b₂ : ∀ k, big.b₂ (e₂ k) = small.b₂ k
  w₃ : ∀ k, big.w₃ (e₂ k) = small.w₃ k
  b₃ : big.b₃ = small.b₃
  extra₁ : ∀ j, j ∉ Set.range e₁ → FirstRemovable big j
  extra₂ : ∀ k, k ∉ Set.range e₂ → SecondRemovable big k

/-- A padding computes the same function as the network it pads. -/
theorem IsPaddingOf.eval_eq {H₁ H₂ : ℕ} {big : Network N H₁ H₂} {small : Network N h₁ h₂}
    {e₁ : Fin h₁ ↪ Fin H₁} {e₂ : Fin h₂ ↪ Fin H₂} (h : IsPaddingOf big small e₁ e₂)
    (x : Point N) : big.eval x = small.eval x := by
  classical
  have hfirst : ∀ k : Fin H₂,
      (∑ j, big.W₂ k j * relu ((∑ i, big.W₁ j i * x i) + big.b₁ j)) =
        ∑ j' : Fin h₁, big.W₂ k (e₁ j') *
          relu ((∑ i, small.W₁ j' i * x i) + small.b₁ j') := by
    intro k
    have hsub : (Finset.univ.map e₁) ⊆ (Finset.univ : Finset (Fin H₁)) :=
      Finset.subset_univ _
    rw [← Finset.sum_subset hsub, Finset.sum_map]
    · refine Finset.sum_congr rfl fun j' _ => ?_
      simp only [h.W₁, h.b₁]
    · intro j _ hj
      have hj' : j ∉ Set.range e₁ := by
        rintro ⟨j', rfl⟩
        exact hj (Finset.mem_map_of_mem e₁ (Finset.mem_univ j'))
      rcases h.extra₁ j hj' with hd | hd
      · rw [hd k, zero_mul]
      · rw [hd.activation_eq_zero x, mul_zero]
  unfold Network.eval
  rw [h.b₃]
  congr 1
  have hsub : (Finset.univ.map e₂) ⊆ (Finset.univ : Finset (Fin H₂)) :=
    Finset.subset_univ _
  rw [← Finset.sum_subset hsub, Finset.sum_map]
  · refine Finset.sum_congr rfl fun k' _ => ?_
    rw [hfirst (e₂ k'), h.w₃, h.b₂]
    simp only [h.W₂]
  · intro k _ hk
    have hk' : k ∉ Set.range e₂ := by
      rintro ⟨k', rfl⟩
      exact hk (Finset.mem_map_of_mem e₂ (Finset.mem_univ k'))
    rcases h.extra₂ k hk' with hd | hd
    · rw [show big.w₃ k = 0 from hd, zero_mul]
    · rw [hd.activation_eq_zero x, mul_zero]

/-- `big` is a *padded solution*: it is a padding of a network of a strictly smaller
architecture which computes the maximum on every real input. -/
def IsPaddedSolution [NeZero N] {H₁ H₂ : ℕ} (big : Network N H₁ H₂) : Prop :=
  ∃ (h₁ h₂ : ℕ) (small : Network N h₁ h₂) (e₁ : Fin h₁ ↪ Fin H₁) (e₂ : Fin h₂ ↪ Fin H₂),
    (h₁ < H₁ ∨ h₂ < H₂) ∧ (∀ x, small.eval x = Maximum N x) ∧ IsPaddingOf big small e₁ e₂

/-- A network is a padded solution exactly when it is exact and has a removable hidden
neuron. This is the bridge between "the component meets the padded image of the fiber of
a strictly smaller architecture" and "the component contains a network with a removable
hidden neuron". -/
theorem isPaddedSolution_iff [NeZero N] {H₁ H₂ : ℕ} (big : Network N H₁ H₂) :
    IsPaddedSolution big ↔ (∀ x, big.eval x = Maximum N x) ∧ HasRemovableNeuron big := by
  constructor
  · rintro ⟨h₁, h₂, small, e₁, e₂, hlt, hsmall, hpad⟩
    refine ⟨fun x => (hpad.eval_eq x).trans (hsmall x), ?_⟩
    rcases hlt with hlt | hlt
    · have hns : ¬ Function.Surjective e₁ := by
        intro hs
        have hle := Fintype.card_le_of_surjective e₁ hs
        simp only [Fintype.card_fin] at hle
        exact absurd hle (not_le.mpr hlt)
      obtain ⟨j, hj⟩ := not_forall.mp hns
      exact Or.inl ⟨j, hpad.extra₁ j (fun ⟨a, ha⟩ => hj ⟨a, ha⟩)⟩
    · have hns : ¬ Function.Surjective e₂ := by
        intro hs
        have hle := Fintype.card_le_of_surjective e₂ hs
        simp only [Fintype.card_fin] at hle
        exact absurd hle (not_le.mpr hlt)
      obtain ⟨k, hk⟩ := not_forall.mp hns
      exact Or.inr ⟨k, hpad.extra₂ k (fun ⟨a, ha⟩ => hk ⟨a, ha⟩)⟩
  · rintro ⟨hexact, hrem⟩
    rcases hrem with ⟨j, hj⟩ | ⟨k, hk⟩
    · cases H₁ with
      | zero => exact j.elim0
      | succ h =>
        refine ⟨h, H₂, removeFirst big j, ⟨j.succAbove, Fin.succAbove_right_injective⟩,
          Function.Embedding.refl _, Or.inl (Nat.lt_succ_self h),
          fun x => (removeFirst_eval big j hj x).trans (hexact x), ?_⟩
        refine ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl,
          ?_, ?_⟩
        · intro j' hj'
          have hjj : j' = j := by
            by_contra hne
            obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
            exact hj' ⟨z, hz⟩
          rw [hjj]
          exact hj
        · intro k hk
          exact (hk ⟨k, rfl⟩).elim
    · cases H₂ with
      | zero => exact k.elim0
      | succ h =>
        refine ⟨H₁, h, removeSecond big k, Function.Embedding.refl _,
          ⟨k.succAbove, Fin.succAbove_right_injective⟩, Or.inr (Nat.lt_succ_self h),
          fun x => (removeSecond_eval big k hk x).trans (hexact x), ?_⟩
        refine ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl,
          ?_, ?_⟩
        · intro j hj
          exact (hj ⟨j, rfl⟩).elim
        · intro k' hk'
          have hkk : k' = k := by
            by_contra hne
            obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
            exact hk' ⟨z, hz⟩
          rw [hkk]
          exact hk

/-! ## Transport of dead neurons along the allowed symmetries -/

/-- Relabelings of the hidden neurons under which each of the four neuron-level
predicates of `b` is the corresponding predicate of `a`. -/
def DeadTransport (a b : Network N h₁ h₂) : Prop :=
  ∃ (π₁ : Equiv.Perm (Fin h₁)) (π₂ : Equiv.Perm (Fin h₂)),
    (∀ j, FirstOutDead b j ↔ FirstOutDead a (π₁ j)) ∧
    (∀ j, FirstInDead b j ↔ FirstInDead a (π₁ j)) ∧
    (∀ k, SecondOutDead b k ↔ SecondOutDead a (π₂ k)) ∧
    (∀ k, SecondInDead b k ↔ SecondInDead a (π₂ k))

theorem DeadTransport.refl (a : Network N h₁ h₂) : DeadTransport a a :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ => Iff.rfl⟩

theorem DeadTransport.symm {a b : Network N h₁ h₂} (h : DeadTransport a b) :
    DeadTransport b a := by
  obtain ⟨π₁, π₂, h1, h2, h3, h4⟩ := h
  refine ⟨π₁.symm, π₂.symm, fun j => ?_, fun j => ?_, fun k => ?_, fun k => ?_⟩
  · simpa only [Equiv.apply_symm_apply] using (h1 (π₁.symm j)).symm
  · simpa only [Equiv.apply_symm_apply] using (h2 (π₁.symm j)).symm
  · simpa only [Equiv.apply_symm_apply] using (h3 (π₂.symm k)).symm
  · simpa only [Equiv.apply_symm_apply] using (h4 (π₂.symm k)).symm

theorem DeadTransport.trans {a b c : Network N h₁ h₂} (hab : DeadTransport a b)
    (hbc : DeadTransport b c) : DeadTransport a c := by
  obtain ⟨π₁, π₂, h1, h2, h3, h4⟩ := hab
  obtain ⟨σ₁, σ₂, g1, g2, g3, g4⟩ := hbc
  exact ⟨σ₁.trans π₁, σ₂.trans π₂, fun j => (g1 j).trans (h1 (σ₁ j)),
    fun j => (g2 j).trans (h2 (σ₁ j)), fun k => (g3 k).trans (h3 (σ₂ k)),
    fun k => (g4 k).trans (h4 (σ₂ k))⟩

theorem deadTransport_scaleFirst (net : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (hs : ∀ j, 0 < s j) : DeadTransport net (scaleFirst net s) := by
  refine ⟨Equiv.refl _, Equiv.refl _, fun j => ?_, fun j => ?_, fun k => Iff.rfl, fun k => ?_⟩
  · change (∀ k, net.W₂ k j / s j = 0) ↔ ∀ k, net.W₂ k j = 0
    simp only [div_eq_zero_iff, (hs j).ne', or_false]
  · change ((∀ i, s j * net.W₁ j i = 0) ∧ s j * net.b₁ j = 0) ↔
      (∀ i, net.W₁ j i = 0) ∧ net.b₁ j = 0
    simp only [mul_eq_zero, (hs j).ne', false_or]
  · change ((∀ j, net.W₂ k j / s j = 0) ∧ net.b₂ k = 0) ↔
      (∀ j, net.W₂ k j = 0) ∧ net.b₂ k = 0
    have : ∀ j, (net.W₂ k j / s j = 0 ↔ net.W₂ k j = 0) := fun j => by
      simp only [div_eq_zero_iff, (hs j).ne', or_false]
    simp only [this]

theorem deadTransport_scaleSecond (net : Network N h₁ h₂) (s : Fin h₂ → ℝ)
    (hs : ∀ k, 0 < s k) : DeadTransport net (scaleSecond net s) := by
  refine ⟨Equiv.refl _, Equiv.refl _, fun j => ?_, fun j => Iff.rfl, fun k => ?_, fun k => ?_⟩
  · change (∀ k, s k * net.W₂ k j = 0) ↔ ∀ k, net.W₂ k j = 0
    have : ∀ k, (s k * net.W₂ k j = 0 ↔ net.W₂ k j = 0) := fun k => by
      simp only [mul_eq_zero, (hs k).ne', false_or]
    simp only [this]
  · change net.w₃ k / s k = 0 ↔ net.w₃ k = 0
    simp only [div_eq_zero_iff, (hs k).ne', or_false]
  · change ((∀ j, s k * net.W₂ k j = 0) ∧ s k * net.b₂ k = 0) ↔
      (∀ j, net.W₂ k j = 0) ∧ net.b₂ k = 0
    simp only [mul_eq_zero, (hs k).ne', false_or]

theorem deadTransport_permuteHidden (net : Network N h₁ h₂) (p : Equiv.Perm (Fin h₁))
    (q : Equiv.Perm (Fin h₂)) : DeadTransport net (permuteHidden net p q) := by
  refine ⟨p, q, fun j => ?_, fun j => Iff.rfl, fun k => Iff.rfl, fun k => ?_⟩
  · change (∀ k, net.W₂ (q k) (p j) = 0) ↔ ∀ k, net.W₂ k (p j) = 0
    constructor
    · intro h k
      simpa only [Equiv.apply_symm_apply] using h (q.symm k)
    · intro h k
      exact h (q k)
  · change ((∀ j, net.W₂ (q k) (p j) = 0) ∧ net.b₂ (q k) = 0) ↔
      (∀ j, net.W₂ (q k) j = 0) ∧ net.b₂ (q k) = 0
    constructor
    · rintro ⟨h, hb⟩
      refine ⟨fun j => ?_, hb⟩
      simpa only [Equiv.apply_symm_apply] using h (p.symm j)
    · rintro ⟨h, hb⟩
      exact ⟨fun j => h (p j), hb⟩

theorem deadTransport_permuteInputs (net : Network N h₁ h₂) (p : Equiv.Perm (Fin N)) :
    DeadTransport net (permuteInputs net p) := by
  refine ⟨Equiv.refl _, Equiv.refl _, fun j => Iff.rfl, fun j => ?_, fun k => Iff.rfl,
    fun k => Iff.rfl⟩
  change ((∀ i, net.W₁ j (p i) = 0) ∧ net.b₁ j = 0) ↔ (∀ i, net.W₁ j i = 0) ∧ net.b₁ j = 0
  constructor
  · rintro ⟨h, hb⟩
    refine ⟨fun i => ?_, hb⟩
    simpa only [Equiv.apply_symm_apply] using h (p.symm i)
  · rintro ⟨h, hb⟩
    exact ⟨fun i => h (p i), hb⟩

theorem deadTransport_of_step [NeZero N] {a b : ExactFiber N h₁ h₂} (h : SymmetryStep a b) :
    DeadTransport a.val b.val := by
  cases h with
  | first s hs => exact deadTransport_scaleFirst a.val s hs
  | second s hs => exact deadTransport_scaleSecond a.val s hs
  | hidden p q => exact deadTransport_permuteHidden a.val p q
  | input p => exact deadTransport_permuteInputs a.val p

/-- Any two representatives of one point of the symmetry quotient have the same dead
neurons up to relabeling. -/
theorem deadTransport_of_symmetry [NeZero N] {a b : ExactFiber N h₁ h₂}
    (h : EqvGen SymmetryStep a b) : DeadTransport a.val b.val := by
  induction h with
  | rel a b h => exact deadTransport_of_step h
  | refl a => exact DeadTransport.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc

private lemma exists_perm_iff {n : ℕ} (π : Equiv.Perm (Fin n)) (P : Fin n → Prop) :
    (∃ j, P (π j)) ↔ ∃ j, P j :=
  ⟨fun ⟨j, hj⟩ => ⟨π j, hj⟩, fun ⟨j, hj⟩ => ⟨π.symm j, by rwa [π.apply_symm_apply]⟩⟩

theorem DeadTransport.hasOutDeadNeuron_iff {a b : Network N h₁ h₂} (h : DeadTransport a b) :
    HasOutDeadNeuron a ↔ HasOutDeadNeuron b := by
  obtain ⟨π₁, π₂, h1, _, h3, _⟩ := h
  unfold HasOutDeadNeuron
  simp only [h1, h3]
  rw [exists_perm_iff π₁ (FirstOutDead a), exists_perm_iff π₂ (SecondOutDead a)]

theorem DeadTransport.hasInDeadNeuron_iff {a b : Network N h₁ h₂} (h : DeadTransport a b) :
    HasInDeadNeuron a ↔ HasInDeadNeuron b := by
  obtain ⟨π₁, π₂, _, h2, _, h4⟩ := h
  unfold HasInDeadNeuron
  simp only [h2, h4]
  rw [exists_perm_iff π₁ (FirstInDead a), exists_perm_iff π₂ (SecondInDead a)]

theorem DeadTransport.hasRemovableNeuron_iff {a b : Network N h₁ h₂}
    (h : DeadTransport a b) : HasRemovableNeuron a ↔ HasRemovableNeuron b := by
  rw [Padding.hasRemovableNeuron_iff, Padding.hasRemovableNeuron_iff, h.hasOutDeadNeuron_iff,
    h.hasInDeadNeuron_iff]

theorem DeadTransport.hasZeroNeuron_iff {a b : Network N h₁ h₂} (h : DeadTransport a b) :
    HasZeroNeuron a ↔ HasZeroNeuron b := by
  obtain ⟨π₁, π₂, h1, h2, h3, h4⟩ := h
  unfold HasZeroNeuron
  simp only [h1, h2, h3, h4]
  rw [exists_perm_iff π₁ (fun j => FirstOutDead a j ∧ FirstInDead a j),
    exists_perm_iff π₂ (fun k => SecondOutDead a k ∧ SecondInDead a k)]

/-- Having a removable hidden neuron is a property of the point of the symmetry
quotient, not of the chosen representative. -/
theorem hasRemovableNeuron_of_symmetry [NeZero N] {a b : ExactFiber N h₁ h₂}
    (h : EqvGen SymmetryStep a b) : HasRemovableNeuron a.val ↔ HasRemovableNeuron b.val :=
  (deadTransport_of_symmetry h).hasRemovableNeuron_iff

theorem hasRemovableNeuron_of_quotientMk_eq [NeZero N] {a b : ExactFiber N h₁ h₂}
    (h : quotientMk a = quotientMk b) : HasRemovableNeuron a.val ↔ HasRemovableNeuron b.val :=
  hasRemovableNeuron_of_symmetry ((quotientMk_eq_iff a b).mp h)

end MaxCaterpillar.Fiber.Padding
