import MaxCaterpillar.Fiber.Count65.Paired.Recession

/-!
# Effective atoms retain all physical zero gates safely

The network itself keeps every physical slot. Only the finite atom index
removes zero jump weights. Arbitrary offsets on a zero-weight gate cannot be
fed into the one-level support lemma.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators

/-- Removing zero weights preserves every atom equation. -/
theorem atomBalance_restrict_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j f : ι → ℝ) (h : Paired65.AtomBalance j f) :
    Paired65.AtomBalance (fun i : {i // j i ≠ 0} => j i.val)
      (fun i : {i // j i ≠ 0} => f i.val) := by
  classical
  intro z
  have hf := h z
  simp only [Paired65.offsetClass, Finset.sum_filter] at hf ⊢
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i => j i ≠ 0)
    (fun i => if f i=z then j i else 0)
  have hz : (∑ i : {i // ¬j i≠0}, if f i.val=z then j i.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : j i.val=0 := not_ne_iff.mp i.property
    simp only [hi, ite_self]
  rw [hz, add_zero] at hs
  rw [hs]
  exact hf

variable {m : ℕ}

/-- A common-slope-zero gate's normalized scalar jump. -/
noncomputable def jumpWeights (d α β : Fin m → ℝ) (k : Fin m) : ℝ :=
  (if α k+β k=0 then d k else 0)*|α k|

lemma jumpWeights_ne_zero_iff (d α β : Fin m → ℝ) (k : Fin m) :
    jumpWeights d α β k ≠ 0 ↔ α k+β k=0 ∧ α k≠0 ∧ d k≠0 := by
  by_cases h : α k+β k=0
  · simp [jumpWeights, h, mul_ne_zero, ne_eq, abs_eq_zero, not_or, and_comm]
  · simp [jumpWeights, h]

/-- This finite index, not the physical network, discards ineffective atoms. -/
abbrev EffectiveAtoms (d α β : Fin m → ℝ) :=
  {k : Fin m // jumpWeights d α β k ≠ 0}

theorem effectiveAtoms_card (d α β : Fin m → ℝ) :
    Fintype.card (EffectiveAtoms d α β) = (activeAtoms d α β).card := by
  classical
  let e : EffectiveAtoms d α β ≃ (activeAtoms d α β) :=
    { toFun := fun k => ⟨k.val, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (jumpWeights_ne_zero_iff d α β k.val).mp k.property⟩⟩
      invFun := fun k => ⟨k.val, (jumpWeights_ne_zero_iff d α β k.val).mpr
        (Finset.mem_filter.mp k.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]

/-- At most four effective atoms occur in a five-slot paired completion. -/
theorem effectiveAtoms_card_le_four (a b : ℝ) (d C α β : Fin m → ℝ)
    (hm : m ≤ 5)
    (h : ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      max (a+q) (b+r) = ∑ k, d k*relu (C k+α k*q+β k*r)) :
    Fintype.card (EffectiveAtoms d α β) ≤ 4 := by
  rw [effectiveAtoms_card]
  exact activeAtoms_card_le_four a b d C α β hm h

/-- The actual max identity gives normalized balance on the effective index. -/
theorem effective_atomBalance_of_max (a b : ℝ) (d C α β : Fin m → ℝ)
    (h : ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      max (a+q) (b+r) = ∑ k, d k*relu (C k+α k*q+β k*r)) :
    Paired65.AtomBalance (fun k : EffectiveAtoms d α β => jumpWeights d α β k.val)
      (fun k : EffectiveAtoms d α β => -(C k.val+α k.val*(b-a))/α k.val) :=
  atomBalance_restrict_nonzero (jumpWeights d α β)
    (fun k => -(C k+α k*(b-a))/α k)
    (atomBalance_of_two_increment_max a b d C α β h)

end MaxCaterpillar.Fiber.Count65.Paired
