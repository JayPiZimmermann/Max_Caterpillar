import MaxCaterpillar.Fiber.Count65.Paired.PairNormalization
import MaxCaterpillar.Fiber.Count65.Paired.EffectiveAtoms

/-! Actual positive normalization of selected common-slope-zero atoms. -/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.PairNormalization

open Absorption
variable {N m k : ℕ}

/-- Divide selected physical rows by the absolute comparison coefficient. -/
noncomputable def atomScales (a : Network N m k) (q : Fin m)
    (S : Finset (Fin k)) (i : Fin k) : ℝ :=
  if i ∈ S then 1 / |a.W₂ i q| else 1

lemma atomScales_pos (a : Network N m k) (q : Fin m) (S : Finset (Fin k))
    (hS : ∀ i ∈ S, a.W₂ i q ≠ 0) : ∀ i, 0 < atomScales a q S i := by
  intro i
  by_cases hi : i ∈ S
  · simp only [atomScales, if_pos hi]
    exact one_div_pos.mpr (abs_pos.mpr (hS i hi))
  · simp [atomScales, hi]

noncomputable def normalizeAtoms (a : Network N m k) (q : Fin m)
    (S : Finset (Fin k)) : Network N m k := scaleSecond a (atomScales a q S)

@[simp] lemma normalizeAtoms_W₁ (a : Network N m k) (q : Fin m) (S : Finset (Fin k)) :
    (normalizeAtoms a q S).W₁ = a.W₁ := rfl
@[simp] lemma normalizeAtoms_b₁ (a : Network N m k) (q : Fin m) (S : Finset (Fin k)) :
    (normalizeAtoms a q S).b₁ = a.b₁ := rfl
@[simp] lemma normalizeAtoms_b₃ (a : Network N m k) (q : Fin m) (S : Finset (Fin k)) :
    (normalizeAtoms a q S).b₃ = a.b₃ := rfl

lemma normalizeAtoms_selected_output (a : Network N m k) (q : Fin m)
    (S : Finset (Fin k)) (i : Fin k) (hi : i ∈ S) :
    (normalizeAtoms a q S).w₃ i = a.w₃ i * |a.W₂ i q| := by
  simp [normalizeAtoms, scaleSecond, atomScales, hi, div_div]

lemma normalizeAtoms_selected_row (a : Network N m k) (q : Fin m)
    (S : Finset (Fin k)) (i : Fin k) (hi : i ∈ S) (j : Fin m) :
    (normalizeAtoms a q S).W₂ i j = a.W₂ i j / |a.W₂ i q| := by
  simp [normalizeAtoms, scaleSecond, atomScales, hi, div_eq_mul_inv, mul_comm]

lemma normalizeAtoms_unselected (a : Network N m k) (q : Fin m)
    (S : Finset (Fin k)) (i : Fin k) (hi : i ∉ S) :
    (normalizeAtoms a q S).W₂ i = a.W₂ i ∧
    (normalizeAtoms a q S).b₂ i = a.b₂ i ∧
    (normalizeAtoms a q S).w₃ i = a.w₃ i := by
  simp [normalizeAtoms, scaleSecond, atomScales, hi]

lemma normalizeAtoms_comparison_pos (a : Network N m k) (q : Fin m)
    (S : Finset (Fin k)) (i : Fin k) (hi : i ∈ S) (hp : 0 < a.W₂ i q) :
    (normalizeAtoms a q S).W₂ i q = 1 := by
  rw [normalizeAtoms_selected_row a q S i hi, abs_of_pos hp, div_self (ne_of_gt hp)]

lemma normalizeAtoms_comparison_neg (a : Network N m k) (q : Fin m)
    (S : Finset (Fin k)) (i : Fin k) (hi : i ∈ S) (hn : a.W₂ i q < 0) :
    (normalizeAtoms a q S).W₂ i q = -1 := by
  rw [normalizeAtoms_selected_row a q S i hi, abs_of_neg hn]
  simp [ne_of_lt hn]

lemma normalizeAtoms_comparison_opposite (a : Network N m k) (q r : Fin m)
    (S : Finset (Fin k)) (i : Fin k) (hi : i ∈ S)
    (hzero : a.W₂ i q + a.W₂ i r = 0) :
    (normalizeAtoms a q S).W₂ i r = -(normalizeAtoms a q S).W₂ i q := by
  rw [normalizeAtoms_selected_row a q S i hi, normalizeAtoms_selected_row a q S i hi]
  have hr : a.W₂ i r = -a.W₂ i q := by linarith only [hzero]
  rw [hr, neg_div]

lemma normalizeAtoms_preact (a : Network N m k) (q : Fin m)
    (S : Finset (Fin k)) (i : Fin k) (hi : i ∈ S) (x : Point N) :
    preact (normalizeAtoms a q S).W₁ (normalizeAtoms a q S).b₁
      ((normalizeAtoms a q S).W₂ i) ((normalizeAtoms a q S).b₂ i) x =
    preact a.W₁ a.b₁ (a.W₂ i) (a.b₂ i) x / |a.W₂ i q| := by
  rw [normalizeAtoms, scaleSecond_preact]
  simp [atomScales, hi, div_eq_mul_inv, mul_comm]

lemma normalizeAtoms_zeroBiases (a : Network N m k) (q : Fin m)
    (S : Finset (Fin k)) (hb : a.HasZeroBiases) : (normalizeAtoms a q S).HasZeroBiases := by
  rcases hb with ⟨hb₁, hb₂, hb₃⟩
  refine ⟨hb₁, ?_, hb₃⟩
  funext i
  simp [normalizeAtoms, scaleSecond, hb₂]

theorem normalizeAtoms_eval (a : Network N m k) (q : Fin m) (S : Finset (Fin k))
    (hS : ∀ i ∈ S, a.W₂ i q ≠ 0) (x : Point N) :
    (normalizeAtoms a q S).eval x = a.eval x :=
  scaleSecond_eval a _ (atomScales_pos a q S hS) x

variable [NeZero N]

noncomputable def normalizeAtomsFiber (a : ExactFiber N m k) (q : Fin m)
    (S : Finset (Fin k)) (hS : ∀ i ∈ S, a.val.W₂ i q ≠ 0) : ExactFiber N m k :=
  scaleSecondFiber (atomScales a.val q S) (atomScales_pos a.val q S hS) a

noncomputable def normalizeAtomsPath (a : ExactFiber N m k) (q : Fin m)
    (S : Finset (Fin k)) (hS : ∀ i ∈ S, a.val.W₂ i q ≠ 0) :
    Path a (normalizeAtomsFiber a q S hS) :=
  scaleSecondPath _ (atomScales_pos a.val q S hS) a

lemma normalizeAtomsPath_fixed (a : ExactFiber N m k) (q : Fin m)
    (S : Finset (Fin k)) (hS : ∀ i ∈ S, a.val.W₂ i q ≠ 0) (t : unitInterval) :
    (normalizeAtomsPath a q S hS t).val.W₁ = a.val.W₁ ∧
    (normalizeAtomsPath a q S hS t).val.b₁ = a.val.b₁ ∧
    (normalizeAtomsPath a q S hS t).val.b₃ = a.val.b₃ := ⟨rfl, rfl, rfl⟩

lemma normalizeAtomsPath_unselected (a : ExactFiber N m k) (q : Fin m)
    (S : Finset (Fin k)) (hS : ∀ i ∈ S, a.val.W₂ i q ≠ 0) (t : unitInterval)
    (i : Fin k) (hi : i ∉ S) :
    (normalizeAtomsPath a q S hS t).val.W₂ i = a.val.W₂ i ∧
    (normalizeAtomsPath a q S hS t).val.b₂ i = a.val.b₂ i ∧
    (normalizeAtomsPath a q S hS t).val.w₃ i = a.val.w₃ i := by
  change (fun j => scaleSegment (atomScales a.val q S) t i * a.val.W₂ i j) = a.val.W₂ i ∧
    scaleSegment (atomScales a.val q S) t i * a.val.b₂ i = a.val.b₂ i ∧
    a.val.w₃ i / scaleSegment (atomScales a.val q S) t i = a.val.w₃ i
  have hs : scaleSegment (atomScales a.val q S) t i = 1 := by
    simp [scaleSegment, atomScales, hi]
  simp [hs]

theorem normalizeAtoms_joinedIn_exact (a : ExactFiber N m k) (q : Fin m)
    (S : Finset (Fin k)) (hS : ∀ i ∈ S, a.val.W₂ i q ≠ 0) :
    JoinedIn (ExactSet N m k) a.val (normalizeAtoms a.val q S) := by
  exact ⟨(normalizeAtomsPath a q S hS).map continuous_subtype_val,
    fun t => (normalizeAtomsPath a q S hS t).property⟩

end MaxCaterpillar.Fiber.Count65.Paired.PairNormalization
