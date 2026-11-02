import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Int.Basic

/-! Finite coordinate-difference frames and integer certificates, independent
of network analysis and real arithmetic. -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.RootFrames
abbrev Root := Fin 4 × Fin 4
abbrev Frame := Finset Root

structure Witness where
  left : Fin 4 → ℤ
  right : Fin 4 → ℤ
  direction : Fin 4 → ℤ
  leftWinner : Fin 4
  rightWinner : Fin 4

/-- The check uses integer arithmetic and four-element bounded quantifiers. -/
def Witness.Checked (F : Frame) (c : Witness) : Prop :=
  (∀ i, c.left i ≤ c.left c.leftWinner) ∧
  (∀ p ∈ F, 0 ≤ c.left p.1 - c.left p.2 → c.direction p.1 = c.direction p.2) ∧
  (∀ i, c.right i ≤ c.right c.rightWinner) ∧
  (∀ p ∈ F, 0 ≤ c.right p.1 - c.right p.2 → c.direction p.1 = c.direction p.2) ∧
  c.direction c.leftWinner ≠ c.direction c.rightWinner

instance checkedDecidable (F : Frame) (c : Witness) : Decidable (c.Checked F) := by
  unfold Witness.Checked
  infer_instance

/-- Every triple contains a root support, equivalently each omitted coordinate
is omitted by one of the four root rows. -/
def CoversTriples (F : Frame) : Prop :=
  ∀ i : Fin 4, ∃ p ∈ F, p.1 ≠ i ∧ p.2 ≠ i

def NoLoops (F : Frame) : Prop := ∀ p ∈ F, p.1 ≠ p.2

/-- A paired-code wall in an arbitrary input labeling. -/
def pairedFrame (p : Fin 4 → Fin 4) : Frame :=
  {(p 0, p 1), (p 2, p 3), (p 1, p 3), (p 3, p 1)}

/-- The outward-star-plus-leaf endpoint in an arbitrary input labeling. -/
def starFrame (p : Fin 4 → Fin 4) : Frame :=
  {(p 0, p 1), (p 1, p 2), (p 3, p 2), (p 0, p 2)}

/-- The actual finite geometric alternatives, not an enumerated survivor label. -/
def NormalForm (F : Frame) : Prop :=
  ∃ p : Fin 4 → Fin 4, Function.Injective p ∧
    (F = pairedFrame p ∨ F = starFrame p)

instance normalFormDecidable (F : Frame) : Decidable (NormalForm F) := by
  unfold NormalForm
  infer_instance

instance coversTriplesDecidable (F : Frame) : Decidable (CoversTriples F) := by
  unfold CoversTriples
  infer_instance

instance noLoopsDecidable (F : Frame) : Decidable (NoLoops F) := by
  unfold NoLoops
  infer_instance

end MaxCaterpillar.Fiber.Count65.RootFrames
