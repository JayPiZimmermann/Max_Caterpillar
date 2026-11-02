import MaxCaterpillar.Fiber.Count65.MatrixForms
import MaxCaterpillar.Fiber.Basic

/-! Closed polynomial conditions for paired first matrices. Degenerate code
lines and zero rows are included; exactness will exclude them later. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.SectorSeparation

abbrev FirstMatrix := Fin 6 → Point 4

def planeRow (a b : ℝ) : Point 4 := ![0,a,0,b]
def rootQ : Point 4 := ![1,-1,0,0]
def rootR : Point 4 := ![0,0,1,-1]

/-- A closed algebraic test for two possibly degenerate opposite directions. -/
def OppositeClosed (a b c d : ℝ) : Prop :=
  a*d-b*c=0 ∧ a*c≤0 ∧ b*d≤0

/-- A closed wedge in all physical first matrices. -/
def PairedClosedRows (A : FirstMatrix) : Prop :=
  0 ≤ A 0 0 ∧ 0 ≤ A 1 2 ∧
  A 0 = A 0 0 • rootQ ∧ A 1 = A 1 2 • rootR ∧
  A 2 = planeRow (A 2 1) (A 2 3) ∧
  A 3 = planeRow (A 3 1) (A 3 3) ∧
  A 4 = planeRow (A 4 1) (A 4 3) ∧
  A 5 = planeRow (A 5 1) (A 5 3) ∧
  OppositeClosed (A 2 1) (A 2 3) (A 3 1) (A 3 3) ∧
  OppositeClosed (A 4 1) (A 4 3) (A 5 1) (A 5 3)

lemma continuous_entry (j : Fin 6) (i : Fin 4) :
    Continuous (fun A : FirstMatrix => A j i) :=
  (continuous_apply i).comp (continuous_apply j)

lemma continuous_planeRow : Continuous (fun p : ℝ × ℝ => planeRow p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_fst
  · exact continuous_const
  · exact continuous_snd

lemma isClosed_opposite (j k : Fin 6) :
    IsClosed {A : FirstMatrix | OppositeClosed (A j 1) (A j 3) (A k 1) (A k 3)} := by
  unfold OppositeClosed
  exact (isClosed_eq ((continuous_entry j 1).mul (continuous_entry k 3) |>.sub
    ((continuous_entry j 3).mul (continuous_entry k 1))) continuous_const).inter
      ((isClosed_le ((continuous_entry j 1).mul (continuous_entry k 1)) continuous_const).inter
        (isClosed_le ((continuous_entry j 3).mul (continuous_entry k 3)) continuous_const))

lemma isClosed_plane (j : Fin 6) :
    IsClosed {A : FirstMatrix | A j = planeRow (A j 1) (A j 3)} :=
  isClosed_eq (continuous_apply j)
    (continuous_planeRow.comp ((continuous_entry j 1).prod_mk (continuous_entry j 3)))

lemma isClosed_pairedClosedRows : IsClosed {A : FirstMatrix | PairedClosedRows A} := by
  unfold PairedClosedRows
  exact (isClosed_le continuous_const (continuous_entry 0 0)).inter
    ((isClosed_le continuous_const (continuous_entry 1 2)).inter
    ((isClosed_eq (continuous_apply 0) ((continuous_entry 0 0).smul continuous_const)).inter
    ((isClosed_eq (continuous_apply 1) ((continuous_entry 1 2).smul continuous_const)).inter
    ((isClosed_plane 2).inter ((isClosed_plane 3).inter ((isClosed_plane 4).inter
    ((isClosed_plane 5).inter ((isClosed_opposite 2 3).inter (isClosed_opposite 4 5)))))))))

lemma planeRow_eq_zero : planeRow 0 0 = 0 := by
  funext i
  fin_cases i <;> rfl

lemma planeRow_nonzero_coordinates (a b : ℝ) (h : planeRow a b ≠ 0) :
    a ≠ 0 ∨ b ≠ 0 := by
  by_contra hn
  have ha : a=0 := by tauto
  have hb : b=0 := by tauto
  exact h (by rw [ha,hb,planeRow_eq_zero])

lemma planeRow_smul (t a b : ℝ) :
    planeRow (t*a) (t*b) = t • planeRow a b := by
  funext i
  fin_cases i <;> simp [planeRow,Pi.smul_apply,smul_eq_mul,
    Matrix.cons_val_zero',Matrix.cons_val_succ']

lemma pairedRows_zero (a b c d : ℝ) : pairedRows a b c d 0 = rootQ := rfl
lemma pairedRows_one (a b c d : ℝ) : pairedRows a b c d 1 = rootR := rfl
lemma pairedRows_two (a b c d : ℝ) : pairedRows a b c d 2 = planeRow a b := rfl
lemma pairedRows_three (a b c d : ℝ) : pairedRows a b c d 3 = planeRow (-a) (-b) := rfl
lemma pairedRows_four (a b c d : ℝ) : pairedRows a b c d 4 = planeRow c d := rfl
lemma pairedRows_five (a b c d : ℝ) : pairedRows a b c d 5 = planeRow (-c) (-d) := rfl

end MaxCaterpillar.Fiber.Count65.SectorSeparation
