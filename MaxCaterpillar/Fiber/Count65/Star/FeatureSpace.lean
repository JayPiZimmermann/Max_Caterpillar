import MaxCaterpillar.Fiber.Star65.Clipping
import MaxCaterpillar.Fiber.Star65.Independence
import MaxCaterpillar.Fiber.Mixed65.Heads
import Mathlib.Topology.Algebra.GroupWithZero

/-! # The actual invariant function space of the positive-path dictionary

The domain consists of real invariant inputs. Clipping rigidity is inherited
from the checked four-ray theorem, so the generic two-head reconstruction
classification applies to this actual function space, including the endpoint.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Star
open MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65

abbrev InvariantState := ℝ × ℝ × ℝ

noncomputable def readout (r A B C D : ℝ) (x : InvariantState) : ℝ :=
  starLinearForm r A B C D x.1 x.2.1 x.2.2

lemma readout_zero (r : ℝ) : readout r 0 0 0 0 = 0 := by
  funext x
  simp [readout, starLinearForm]

lemma readout_add (r A B C D E F G H : ℝ) :
    readout r (A + E) (B + F) (C + G) (D + H) =
      readout r A B C D + readout r E F G H := by
  funext x
  simp only [readout, starLinearForm, Pi.add_apply]
  ring

lemma readout_smul (s r A B C D : ℝ) :
    readout r (s * A) (s * B) (s * C) (s * D) = s • readout r A B C D := by
  funext x
  simp only [readout, starLinearForm, Pi.smul_apply, smul_eq_mul]
  ring

/-- Exactly the actual four-feature function span, rather than an abstract
coefficient space or observations at selected inputs. -/
noncomputable def featureSpace (r : ℝ) : Submodule ℝ (InvariantState → ℝ) where
  carrier := {f | ∃ A B C D : ℝ, f = readout r A B C D}
  zero_mem' := ⟨0, 0, 0, 0, (readout_zero r).symm⟩
  add_mem' := by
    rintro f g ⟨A, B, C, D, rfl⟩ ⟨E, F, G, H, rfl⟩
    exact ⟨A + E, B + F, C + G, D + H, (readout_add r A B C D E F G H).symm⟩
  smul_mem' := by
    rintro s f ⟨A, B, C, D, rfl⟩
    exact ⟨s * A, s * B, s * C, s * D, (readout_smul s r A B C D).symm⟩

theorem readout_mem_featureSpace (r A B C D : ℝ) :
    readout r A B C D ∈ featureSpace r := ⟨A, B, C, D, rfl⟩

/-- Readout of a four-coordinate coefficient vector. -/
noncomputable def coefficientReadout (r : ℝ) (a : Fin 4 → ℝ) : featureSpace r :=
  ⟨readout r (a 0) (a 1) (a 2) (a 3), readout_mem_featureSpace r _ _ _ _⟩

/-- Four actual evaluations recover every coefficient. -/
noncomputable def recoverReadout (r : ℝ) (f : featureSpace r) : Fin 4 → ℝ :=
  ![f.val (r, -1, 0) / r, f.val (-r, 1, 0), f.val (0, 0, 1),
    (f.val (r, 0, 0) - f.val (r, -1, 0)) / r]

lemma recover_coefficientReadout {r : ℝ} (hr : 0 < r) (a : Fin 4 → ℝ) :
    recoverReadout r (coefficientReadout r a) = a := by
  funext i
  fin_cases i <;>
    simp only [recoverReadout, coefficientReadout, readout, starLinearForm,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      max_eq_right hr.le, max_eq_left (neg_nonpos.mpr hr.le)]
  all_goals try norm_num
  all_goals try field_simp [ne_of_gt hr]
  all_goals first | rfl | ring

lemma coefficientReadout_recover {r : ℝ} (hr : 0 < r) (f : featureSpace r) :
    coefficientReadout r (recoverReadout r f) = f := by
  rcases f with ⟨f, A, B, C, D, rfl⟩
  have h := recover_coefficientReadout hr ![A,B,C,D]
  have he : coefficientReadout r ![A,B,C,D] =
      (⟨readout r A B C D, A,B,C,D,rfl⟩ : featureSpace r) := rfl
  rw [← he, h]

lemma continuous_coefficientReadout (r : ℝ) : Continuous (coefficientReadout r) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro x
  have h (i : Fin 4) : Continuous (fun a : Fin 4 → ℝ => a i) := continuous_apply i
  exact ((((h 0).mul continuous_const).add ((h 1).mul continuous_const)).add
    ((h 2).mul continuous_const)).add ((h 3).mul continuous_const)

lemma continuous_recoverReadout (r : ℝ) : Continuous (recoverReadout r) := by
  have h (x : InvariantState) : Continuous (fun f : featureSpace r => f.val x) :=
    (continuous_apply x).comp continuous_subtype_val
  apply continuous_pi
  intro i
  fin_cases i
  · exact (h (r,-1,0)).div_const r
  · exact h (-r,1,0)
  · exact h (0,0,1)
  · exact ((h (r,0,0)).sub (h (r,-1,0))).div_const r

/-- The actual pointwise-function subspace and physical readout coefficient
space carry the same topology, by an explicit finite-evaluation inverse. -/
noncomputable def coefficientReadoutHomeomorph {r : ℝ} (hr : 0 < r) :
    (Fin 4 → ℝ) ≃ₜ featureSpace r where
  toFun := coefficientReadout r
  invFun := recoverReadout r
  left_inv := recover_coefficientReadout hr
  right_inv := coefficientReadout_recover hr
  continuous_toFun := continuous_coefficientReadout r
  continuous_invFun := continuous_recoverReadout r

/-- Every readout has a nonnegative decomposition in the same feature space. -/
theorem exists_nonnegative_decomposition {r : ℝ} {L : InvariantState → ℝ}
    (hL : L ∈ featureSpace r) :
    ∃ A B : featureSpace r, (∀ x, 0 ≤ A.val x) ∧ (∀ x, 0 ≤ B.val x) ∧
      A.val - B.val = L := by
  rcases hL with ⟨a,b,c,d,rfl⟩
  let A : featureSpace r := coefficientReadout r ![relu a,relu b,relu c,relu d]
  let B : featureSpace r := coefficientReadout r ![relu (-a),relu (-b),relu (-c),relu (-d)]
  refine ⟨A,B,?_,?_,?_⟩
  · intro x
    exact add_nonneg (add_nonneg
      (add_nonneg (mul_nonneg (relu_nonneg _) (le_max_left _ _))
        (mul_nonneg (relu_nonneg _) (le_max_left _ _)))
      (mul_nonneg (relu_nonneg _) (le_max_left _ _)))
      (mul_nonneg (relu_nonneg _) (le_max_left _ _))
  · intro x
    exact add_nonneg (add_nonneg
      (add_nonneg (mul_nonneg (relu_nonneg _) (le_max_left _ _))
        (mul_nonneg (relu_nonneg _) (le_max_left _ _)))
      (mul_nonneg (relu_nonneg _) (le_max_left _ _)))
      (mul_nonneg (relu_nonneg _) (le_max_left _ _))
  · funext x
    change (relu a * max 0 x.1 + relu b * max 0 x.2.1 +
      relu c * max 0 x.2.2 + relu d * max 0 (x.1+r*x.2.1)) -
      (relu (-a) * max 0 x.1 + relu (-b) * max 0 x.2.1 +
      relu (-c) * max 0 x.2.2 + relu (-d) * max 0 (x.1+r*x.2.1)) = _
    have ha := relu_sub_relu_neg a
    have hb := relu_sub_relu_neg b
    have hc := relu_sub_relu_neg c
    have hd := relu_sub_relu_neg d
    dsimp only [readout, starLinearForm]
    linear_combination ha * max 0 x.1 + hb * max 0 x.2.1 +
      hc * max 0 x.2.2 + hd * max 0 (x.1+r*x.2.1)

/-- Clipping rigidity on the complete invariant input domain. -/
theorem clippingRigid_featureSpace {r : ℝ} (hr : 0 < r) :
    Mixed65.ClippingRigid (featureSpace r) := by
  intro f hf hclip
  rcases hf with ⟨A, B, C, D, rfl⟩
  rcases hclip with ⟨E, F, G, H, h⟩
  have he : ∀ q v w : ℝ,
      max 0 (starLinearForm r A B C D q v w) =
        starLinearForm r E F G H q v w := by
    intro q v w
    exact congrFun h (q, v, w)
  rcases starLinearForm_clipping hr he with hn | hn
  · exact Or.inl (fun x => hn x.1 x.2.1 x.2.2)
  · exact Or.inr (fun x => hn x.1 x.2.1 x.2.2)

/-- Every exact two-head completion is one of the two physical reconstruction
types. The input is an actual-function identity, not formal coefficients. -/
theorem heads_reconstructs_iff {r : ℝ} (hr : 0 < r)
    (h : Mixed65.Heads InvariantState) (L : InvariantState → ℝ)
    (hA : h.A ∈ featureSpace r) (hB : h.B ∈ featureSpace r)
    (hL : L ∈ featureSpace r) :
    h.Reconstructs L ↔ h.IsSigned L ∨ h.IsSplitHybrid L :=
  Mixed65.Heads.reconstructs_iff_signed_or_splitHybrid (featureSpace r)
    (clippingRigid_featureSpace hr) h L hA hB hL

/-- Arbitrary orientation corrections cannot annihilate the first-branch
remainder; this includes every binary orientation choice. -/
theorem branchI_oriented_remainder_nonzero {r k : ℝ} (hr : 0 < r) (hk : k ≤ 0)
    (i j z : ℝ) : ∃ q v w : ℝ,
      max 0 w + i * (comparison r q v - max 0 w) +
        j * (max 0 v - max 0 w + k * max 0 q) -
        z * (comparison r q v - max 0 q - max 0 w + k * max 0 q) ≠ 0 := by
  by_contra hn
  push_neg at hn
  have H : ∀ q v w : ℝ,
      1 * max 0 w + i * (comparison r q v - max 0 w) +
        j * (max 0 v - max 0 w + k * max 0 q) +
        (-z) * (comparison r q v - max 0 q - max 0 w + k * max 0 q) = 0 := by
    intro q v w
    simpa only [one_mul, neg_mul, sub_eq_add_neg] using hn q v w
  have h := (branchI_core_independent hr hk 1 i j (-z) H).1
  norm_num at h

/-- The second branch has the same nonzero-remainder conclusion, even at
its finite slack boundary and at the star endpoint. -/
theorem branchII_oriented_remainder_nonzero {r h : ℝ} (hr : 0 < r) (hh : h ≤ -1)
    (i j z : ℝ) : ∃ q v w : ℝ,
      max 0 w + i * (comparison r q v - max 0 w + h * max 0 v) +
        j * (max 0 q + max 0 v - max 0 w) -
        z * (max 0 q + (1 + h) * max 0 v - max 0 w) ≠ 0 := by
  by_contra hn
  push_neg at hn
  have H : ∀ q v w : ℝ,
      1 * max 0 w + i * (comparison r q v - max 0 w + h * max 0 v) +
        j * (max 0 q + max 0 v - max 0 w) +
        (-z) * (max 0 q + (1 + h) * max 0 v - max 0 w) = 0 := by
    intro q v w
    simpa only [one_mul, neg_mul, sub_eq_add_neg] using hn q v w
  have h := (branchII_core_independent hr hh 1 i j (-z) H).1
  norm_num at h

/-- Nonzero remainders make the two head types genuinely disjoint. -/
theorem signed_disjoint_splitHybrid {h : Mixed65.Heads InvariantState}
    {L : InvariantState → ℝ} (hL : ∃ x, L x ≠ 0) (hs : h.IsSigned L) :
    ¬ h.IsSplitHybrid L :=
  Mixed65.Heads.signed_not_splitHybrid hL hs

end MaxCaterpillar.Fiber.Count65.Star
