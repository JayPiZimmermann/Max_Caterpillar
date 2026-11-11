import MaxCaterpillar.Fiber.Minimal63.Paths

/-! # A positive common-offset family in the physical Max4 network model -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.GatingAbstractions
open BigOperators Frontier

/-- Every common-offset coefficient is positive when `c > 0`. -/
def offset (c : ℝ) : Fin 6 → ℝ := ![c, 1, 1, 1, 1, 1]

/-- Ordinary bias-free (6,3) networks, with a fixed first hidden layer. -/
noncomputable def family (c : ℝ) : Network 4 6 3 := splitNet (offset c)

lemma offset_pos {c : ℝ} (hc : 0 < c) (j : Fin 6) : 0 < offset c j := by
  fin_cases j <;> simpa [offset] using hc <;> norm_num [offset]

/-- Every member computes Max4 on all real inputs. -/
theorem family_eval (c : ℝ) (hc : 0 ≤ c) (x : Point 4) :
    (family c).eval x = Maximum 4 x := by
  apply splitNet_eval
  intro j
  fin_cases j <;> simp [offset] <;> exact hc

/-- The family is continuous in the actual topology of all network parameters. -/
theorem continuous_family : Continuous family := by
  apply continuous_splitNet.comp
  apply continuous_pi
  intro j
  fin_cases j <;> simp only [offset, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons] <;> continuity

/-- Explicit inputs for the two different interior collision equations. -/
noncomputable def inputX : Point 4 := ![2, 1, 3, 1]
noncomputable def inputY : Point 4 := ![2, 3/2, 3, 1]
noncomputable def inputZ : Point 4 := ![5/2, 2, 3, 1]
noncomputable def inputW : Point 4 := ![5, 1, 3, 1]

@[simp] lemma inputX_0 : inputX 0 = 2 := rfl
@[simp] lemma inputX_1 : inputX 1 = 1 := rfl
@[simp] lemma inputX_2 : inputX 2 = 3 := rfl
@[simp] lemma inputX_3 : inputX 3 = 1 := rfl
@[simp] lemma inputY_0 : inputY 0 = 2 := rfl
@[simp] lemma inputY_1 : inputY 1 = 3/2 := rfl
@[simp] lemma inputY_2 : inputY 2 = 3 := rfl
@[simp] lemma inputY_3 : inputY 3 = 1 := rfl
@[simp] lemma inputZ_0 : inputZ 0 = 5/2 := rfl
@[simp] lemma inputZ_1 : inputZ 1 = 2 := rfl
@[simp] lemma inputZ_2 : inputZ 2 = 3 := rfl
@[simp] lemma inputZ_3 : inputZ 3 = 1 := rfl
@[simp] lemma inputW_0 : inputW 0 = 5 := rfl
@[simp] lemma inputW_1 : inputW 1 = 1 := rfl
@[simp] lemma inputW_2 : inputW 2 = 3 := rfl
@[simp] lemma inputW_3 : inputW 3 = 1 := rfl

lemma pairedFeatures_inputX : pairedFeatures inputX = ![1,2,1,0,1,0] := by
  change ![relu (2-1),relu (3-1),relu 1,relu (-1),relu 1,relu (-1)] = _
  norm_num [relu]

lemma pairedFeatures_inputY : pairedFeatures inputY = ![1/2,2,3/2,0,1,0] := by
  change ![relu (2-3/2),relu (3-1),relu (3/2),relu (-(3/2)),relu 1,relu (-1)] = _
  norm_num [relu]

lemma pairedFeatures_inputZ : pairedFeatures inputZ = ![1/2,2,2,0,1,0] := by
  change ![relu (5/2-2),relu (3-1),relu 2,relu (-2),relu 1,relu (-1)] = _
  norm_num [relu]

lemma pairedFeatures_inputW : pairedFeatures inputW = ![4,2,1,0,1,0] := by
  change ![relu (5-1),relu (3-1),relu 1,relu (-1),relu 1,relu (-1)] = _
  norm_num [relu]

/-- All three sign statuses are compared, including zero preactivations. -/
def SameSign (a b : ℝ) : Prop :=
  (a < 0 ↔ b < 0) ∧ (a = 0 ↔ b = 0) ∧ (0 < a ↔ 0 < b)

lemma sameSign_refl (a : ℝ) : SameSign a a := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

lemma sameSign_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : a = 0 ↔ b = 0) : SameSign a b := by
  refine ⟨iff_of_false (not_lt_of_ge ha) (not_lt_of_ge hb), hz, ?_⟩
  constructor
  · intro h
    by_contra hn
    have hb0 : b = 0 := le_antisymm (le_of_not_gt hn) hb
    have ha0 := hz.mpr hb0
    linarith
  · intro h
    by_contra hn
    have ha0 : a = 0 := le_antisymm (le_of_not_gt hn) ha
    have hb0 := hz.mp ha0
    linarith

end MaxCaterpillar.Fiber.GatingAbstractions
