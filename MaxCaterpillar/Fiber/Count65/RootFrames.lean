import MaxCaterpillar.Fiber.First65.ActiveSpan
import MaxCaterpillar.Fiber.Count65.RootFrameData

/-! # A finite cell obstruction for four coordinate-difference directions

A certificate consists of two integer test points with a common invisible
indicator direction, but different winning coordinates along that direction.
The decoder and the coefficients of its linear skip are arbitrary real objects.
Thus a checked certificate excludes every real decoder, not just a coefficient
search. The finite table and its exhaustive coverage are separate modules.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.RootFrames
open BigOperators MaxCaterpillar.Frontier

/-- The exact coordinate-difference covector; loops are filtered by the classifier. -/
def row (p : Root) : Point 4 :=
  fun i => (if i = p.1 then 1 else 0) - (if i = p.2 then 1 else 0)

lemma lin_row (p : Root) (x : Point 4) : lin (row p) x = x p.1 - x p.2 := by
  simp [lin, row, sub_mul, Finset.sum_sub_distrib, ite_mul]

lemma row_zero_iff (p : Root) (hp : p.1 ≠ p.2) (i : Fin 4) :
    row p i = 0 ↔ i ≠ p.1 ∧ i ≠ p.2 := by
  by_cases hi : i = p.1
  · subst i
    simp [row, hp]
  · by_cases hj : i = p.2
    · subst i
      simp [row, hp, Ne.symm hp]
    · simp [row, hi, hj]

/-- An arbitrary homogeneous-feature decoder plus an arbitrary linear skip. -/
def Factors (F : Frame) : Prop :=
  ∃ ell : Point 4, ∃ Phi : (F → ℝ) → ℝ,
    ∀ x, Maximum 4 x = lin ell x + Phi (fun p => relu (lin (row p.val) x))

/-- The two cell conditions contradict the same linear readout. -/
theorem not_factors_of_checked (F : Frame) (c : Witness) (hc : c.Checked F) :
    ¬ Factors F := by
  classical
  rintro ⟨ell, Phi, h⟩
  let ql : Point 4 := fun i => (c.left i : ℝ)
  let qr : Point 4 := fun i => (c.right i : ℝ)
  let w : Point 4 := fun i => (c.direction i : ℝ)
  have hl : ql c.leftWinner = Maximum 4 ql := by
    symm
    exact Maximum_eq_of ql _ c.leftWinner rfl (fun i => by dsimp [ql]; exact_mod_cast hc.1 i)
  have hr : qr c.rightWinner = Maximum 4 qr := by
    symm
    exact Maximum_eq_of qr _ c.rightWinner rfl (fun i => by dsimp [qr]; exact_mod_cast hc.2.2.1 i)
  have hkl : ∀ p : F, 0 ≤ lin (row p.val) ql → lin (row p.val) w = 0 := by
    intro p hp
    rw [lin_row] at hp ⊢
    have hi : (0 : ℤ) ≤ c.left p.val.1 - c.left p.val.2 := by
      dsimp [ql] at hp
      exact_mod_cast hp
    have he := hc.2.1 p.val p.property hi
    change (c.direction p.val.1 : ℝ) - (c.direction p.val.2 : ℝ) = 0
    exact sub_eq_zero.mpr (by exact_mod_cast he)
  have hkr : ∀ p : F, 0 ≤ lin (row p.val) qr → lin (row p.val) w = 0 := by
    intro p hp
    rw [lin_row] at hp ⊢
    have hi : (0 : ℤ) ≤ c.right p.val.1 - c.right p.val.2 := by
      dsimp [qr] at hp
      exact_mod_cast hp
    have he := hc.2.2.2.1 p.val p.property hi
    change (c.direction p.val.1 : ℝ) - (c.direction p.val.2 : ℝ) = 0
    exact sub_eq_zero.mpr (by exact_mod_cast he)
  have hel := active_kernel_top_coordinate (fun p : F => row p.val) ell Phi h
    ql w hkl c.leftWinner hl
  have her := active_kernel_top_coordinate (fun p : F => row p.val) ell Phi h
    qr w hkr c.rightWinner hr
  have he : w c.leftWinner = w c.rightWinner := hel.trans her.symm
  apply hc.2.2.2.2
  dsimp [w] at he
  exact_mod_cast he

#print axioms not_factors_of_checked
end MaxCaterpillar.Fiber.Count65.RootFrames
