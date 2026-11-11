import MaxCaterpillar.Frontier.StarCertificate.Checker.Basic

/-! # Exact infeasible-prefix and vanishing-face certificates -/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def FarkasValid {m n : ℕ} (A : Fin m → RationalForm n) (p : Context m)
    (w : Fin m → ℚ) : Prop :=
  (∀ j, p j = none → w j = 0) ∧
  (∀ j s, p j = some s → s ≠ .zero → 0 ≤ w j) ∧
  (∃ j s, p j = some s ∧ s ≠ .zero ∧ 0 < w j) ∧
  (∀ i, ∑ j, w j * oriented A p j i = 0)

instance farkasValidDecidable {m n : ℕ} (A : Fin m → RationalForm n)
    (p : Context m) (w : Fin m → ℚ) : Decidable (FarkasValid A p w) := by
  unfold FarkasValid
  infer_instance

/-- A rational Farkas certificate excludes every real vector in the prefix,
including prefixes containing equality constraints. -/
theorem farkas_impossible {m n : ℕ} (A : Fin m → RationalForm n)
    (p : Context m) (w : Fin m → ℚ) (h : FarkasValid A p w)
    (x : Fin n → ℝ) (hp : Holds A p x) : False := by
  have hnonneg : ∀ j, 0 ≤ (w j : ℝ) * evalForm (oriented A p j) x := by
    intro j
    cases hj : p j with
    | none =>
      simp only [h.1 j hj, Rat.cast_zero, zero_mul]
      exact le_refl 0
    | some s =>
      have hs := hp j s hj
      cases s with
      | neg =>
        have hw : 0 ≤ (w j : ℝ) := by
          exact_mod_cast h.2.1 j .neg hj (by decide)
        rw [evalForm_oriented_neg A p j x hj]
        exact mul_nonneg hw (neg_nonneg.mpr hs.le)
      | zero =>
        have hn : p j ≠ some .neg := by rw [hj]; decide
        rw [evalForm_oriented_other A p j x hn, hs, mul_zero]
      | pos =>
        have hw : 0 ≤ (w j : ℝ) := by
          exact_mod_cast h.2.1 j .pos hj (by decide)
        have hn : p j ≠ some .neg := by rw [hj]; decide
        rw [evalForm_oriented_other A p j x hn]
        exact mul_nonneg hw hs.le
  obtain ⟨j, s, hj, hs, hw⟩ := h.2.2.1
  have hstrict : 0 < (w j : ℝ) * evalForm (oriented A p j) x := by
    have hw' : 0 < (w j : ℝ) := by exact_mod_cast hw
    have hv := hp j s hj
    cases s with
    | neg =>
      rw [evalForm_oriented_neg A p j x hj]
      exact mul_pos hw' (neg_pos.mpr hv)
    | zero => exact False.elim (hs rfl)
    | pos =>
      have hn : p j ≠ some .neg := by rw [hj]; decide
      rw [evalForm_oriented_other A p j x hn]
      exact mul_pos hw' hv
  have hsum : 0 < ∑ j, (w j : ℝ) * evalForm (oriented A p j) x :=
    Finset.sum_pos' (fun j _ => hnonneg j) ⟨j, Finset.mem_univ j, hstrict⟩
  have hvec : (fun i => ∑ j, w j * oriented A p j i) = (0 : RationalForm n) :=
    funext h.2.2.2
  have he := evalForm_combination (fun j => oriented A p j) w x
  rw [hvec, evalForm_zero] at he
  exact (ne_of_gt hsum) he.symm

def ZeroSpanValid {m n : ℕ} (A : Fin m → RationalForm n) (p : Context m)
    (a : RationalForm n) (w : Fin m → ℚ) : Prop :=
  (∀ j, p j ≠ some .zero → w j = 0) ∧
  (∀ i, a i = ∑ j, w j * A j i)

instance zeroSpanValidDecidable {m n : ℕ} (A : Fin m → RationalForm n)
    (p : Context m) (a : RationalForm n) (w : Fin m → ℚ) :
    Decidable (ZeroSpanValid A p a w) := by
  unfold ZeroSpanValid
  infer_instance

/-- A symbolic coefficient identity modulo the span of zero forms is
valid on the entire real face, including lower-dimensional boundaries. -/
theorem zeroSpan_vanishes {m n : ℕ} (A : Fin m → RationalForm n)
    (p : Context m) (a : RationalForm n) (w : Fin m → ℚ)
    (h : ZeroSpanValid A p a w) (x : Fin n → ℝ) (hp : Holds A p x) :
    evalForm a x = 0 := by
  have ha : a = fun i => ∑ j, w j * A j i := funext h.2
  rw [ha, evalForm_combination]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : p j = some .zero
  · have hz := hp j .zero hj
    rw [hz, mul_zero]
  · rw [h.1 j hj, Rat.cast_zero, zero_mul]

end MaxCaterpillar.Frontier.StarCertificate
