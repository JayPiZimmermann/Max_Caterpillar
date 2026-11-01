import MaxCaterpillar.Fiber.Separation

/-! # Two distinct symmetry classes in the actual Max4 width-(6,5) fiber

The mixed sector is nonempty, and a padded minimal construction is outside it.
The invariant used to separate these symmetry classes only records whether
each first hidden row has two distinct zero coordinate entries. This invariant
is not claimed to be locally constant on the exact fiber; the clopen-sector
argument is a separate obligation.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

variable {N h₁ h₂ : ℕ}

/-- A coordinate sparsity predicate, used only as an invariant of the allowed
symmetries and not as a connected-component label. -/
def TwoZeroEntriesPerFirstRow (net : Network N h₁ h₂) : Prop :=
  ∀ j, ∃ i k, i ≠ k ∧ net.W₁ j i = 0 ∧ net.W₁ j k = 0

theorem twoZero_scaleFirst (net : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (hs : ∀ j, 0 < s j) :
    TwoZeroEntriesPerFirstRow (scaleFirst net s) ↔ TwoZeroEntriesPerFirstRow net := by
  constructor
  · intro h j
    obtain ⟨i, k, hik, hi, hk⟩ := h j
    exact ⟨i, k, hik, (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hs j)),
      (mul_eq_zero.mp hk).resolve_left (ne_of_gt (hs j))⟩
  · intro h j
    obtain ⟨i, k, hik, hi, hk⟩ := h j
    refine ⟨i, k, hik, ?_, ?_⟩
    · change s j * net.W₁ j i = 0
      rw [hi, mul_zero]
    · change s j * net.W₁ j k = 0
      rw [hk, mul_zero]

theorem twoZero_scaleSecond (net : Network N h₁ h₂) (s : Fin h₂ → ℝ) :
    TwoZeroEntriesPerFirstRow (scaleSecond net s) ↔ TwoZeroEntriesPerFirstRow net := Iff.rfl

theorem twoZero_permuteHidden (net : Network N h₁ h₂)
    (p : Equiv.Perm (Fin h₁)) (q : Equiv.Perm (Fin h₂)) :
    TwoZeroEntriesPerFirstRow (permuteHidden net p q) ↔ TwoZeroEntriesPerFirstRow net := by
  constructor
  · intro h j
    simpa only [permuteHidden, Equiv.apply_symm_apply] using h (p.symm j)
  · intro h j
    exact h (p j)

theorem twoZero_permuteInputs (net : Network N h₁ h₂) (p : Equiv.Perm (Fin N)) :
    TwoZeroEntriesPerFirstRow (permuteInputs net p) ↔ TwoZeroEntriesPerFirstRow net := by
  constructor
  · intro h j
    obtain ⟨i, k, hik, hi, hk⟩ := h j
    exact ⟨p i, p k, fun h => hik (p.injective h), hi, hk⟩
  · intro h j
    obtain ⟨i, k, hik, hi, hk⟩ := h j
    refine ⟨p.symm i, p.symm k, fun h => hik (p.symm.injective h), ?_, ?_⟩
    · change net.W₁ j (p (p.symm i)) = 0
      simpa only [p.apply_symm_apply] using hi
    · change net.W₁ j (p (p.symm k)) = 0
      simpa only [p.apply_symm_apply] using hk

theorem twoZero_of_symmetryStep [NeZero N] {a b : ExactFiber N h₁ h₂}
    (h : SymmetryStep a b) :
    TwoZeroEntriesPerFirstRow a.val ↔ TwoZeroEntriesPerFirstRow b.val := by
  cases h with
  | first s hs => exact (twoZero_scaleFirst a.val s hs).symm
  | second s hs => exact (twoZero_scaleSecond a.val s).symm
  | hidden p q => exact (twoZero_permuteHidden a.val p q).symm
  | input p => exact (twoZero_permuteInputs a.val p).symm

theorem twoZero_of_symmetry [NeZero N] {a b : ExactFiber N h₁ h₂}
    (h : EqvGen SymmetryStep a b) :
    TwoZeroEntriesPerFirstRow a.val ↔ TwoZeroEntriesPerFirstRow b.val := by
  induction h with
  | rel a b h => exact twoZero_of_symmetryStep h
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc

/-- The mixed row has exactly one zero coordinate when its parameter is positive. -/
theorem firstRows_mixed_zero_iff {t : ℝ} (ht : 0 < t) (i : Fin 4) :
    firstRows t 3 i = 0 ↔ i = 3 := by
  constructor
  · intro hi
    fin_cases i
    · change t = 0 at hi
      exact False.elim ((ne_of_gt ht) hi)
    · change -(t + 1) = 0 at hi
      exfalso
      linarith only [ht, hi]
    · change (1 : ℝ) = 0 at hi
      norm_num at hi
    · rfl
  · rintro rfl
    rfl

theorem not_twoZero_of_firstRows {net : Network 4 6 5} {t : ℝ}
    (ht : 0 < t) (hrows : net.W₁ = firstRows t) :
    ¬ TwoZeroEntriesPerFirstRow net := by
  intro h
  obtain ⟨i, k, hik, hi, hk⟩ := h 3
  rw [hrows] at hi hk
  exact hik (((firstRows_mixed_zero_iff ht i).mp hi).trans
    ((firstRows_mixed_zero_iff ht k).mp hk).symm)

/-- A concrete point in the normalized mixed first-layer sector. -/
noncomputable def mixedPoint : ExactFiber 4 6 5 :=
  ⟨branchANet 1 1, branchANet_eval 1 1 (by norm_num) (by norm_num)⟩

theorem mixedPoint_mem_seed : mixedPoint ∈ seed := by
  exact ⟨1, by norm_num, rfl⟩

theorem seed_nonempty : seed.Nonempty := ⟨mixedPoint, mixedPoint_mem_seed⟩

theorem mixedPoint_mem_sector : mixedPoint ∈ sector :=
  subset_symmetrySaturation seed mixedPoint_mem_seed

theorem sector_nonempty : sector.Nonempty := ⟨mixedPoint, mixedPoint_mem_sector⟩

/-- The minimal width-(6,3) construction with two unused second-layer neurons. -/
noncomputable def paddedMinimalPoint : ExactFiber 4 6 5 :=
  ⟨Frontier.maxFourNet.padSecond 2, fun x => by
    rw [Network.padSecond_eval, Frontier.maxFourNet_eval]⟩

theorem paddedMinimalPoint_twoZero : TwoZeroEntriesPerFirstRow paddedMinimalPoint.val := by
  intro j
  fin_cases j
  · exact ⟨2, 3, by decide, rfl, rfl⟩
  · exact ⟨0, 1, by decide, rfl, rfl⟩
  · exact ⟨0, 2, by decide, rfl, rfl⟩
  · exact ⟨0, 2, by decide, rfl, rfl⟩
  · exact ⟨0, 1, by decide, rfl, rfl⟩
  · exact ⟨0, 1, by decide, rfl, rfl⟩

theorem paddedMinimalPoint_not_mem_sector : paddedMinimalPoint ∉ sector := by
  rintro ⟨a, ⟨t, ht, hrows⟩, ha⟩
  exact not_twoZero_of_firstRows ht hrows
    ((twoZero_of_symmetry ha).mpr paddedMinimalPoint_twoZero)

theorem sector_compl_nonempty : sectorᶜ.Nonempty :=
  ⟨paddedMinimalPoint, paddedMinimalPoint_not_mem_sector⟩

/-- The exhibited networks represent distinct symmetry classes. Separation of
their connected components additionally requires the clopen-sector theorem. -/
theorem mixedPoint_quotient_ne_paddedMinimalPoint :
    quotientMk mixedPoint ≠ quotientMk paddedMinimalPoint := by
  intro h
  exact paddedMinimalPoint_not_mem_sector
    ((sector_invariant mixedPoint paddedMinimalPoint
      ((quotientMk_eq_iff mixedPoint paddedMinimalPoint).mp h)).mp mixedPoint_mem_sector)

end MaxCaterpillar.Fiber.Mixed65
