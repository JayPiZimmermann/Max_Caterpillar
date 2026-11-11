import MaxCaterpillar.Frontier.Constructions
import MaxCaterpillar.Frontier.Main

/-! # Exact families and a coefficient gap in the minimal Max4 fiber

These results concern actual `Network 4 6 3` parameters or explicitly stated
functional identities. They do not assume or assert the exhaustive normal-form
classification needed to count components of the full parameter fiber.
-/

set_option autoImplicit false

namespace MaxCaterpillar
namespace Fiber

open BigOperators Frontier

private lemma relu_eq_argument_of_pos {a : ℝ} (ha : 0 < relu a) : relu a = a := by
  rcases le_total 0 a with h | h
  · exact relu_of_nonneg h
  · rw [relu_of_nonpos h] at ha
    exact False.elim (lt_irrefl 0 ha)

/-- A two-ReLU representation of the affine ray `r - 1` has a gap in the
negative neuron's slope: a strictly negative slope must equal `-1`.
The identity is required for every nonnegative real `r`. -/
theorem negative_base_slope_eq_neg_one (c d β δ : ℝ)
    (h : ∀ r : ℝ, 0 ≤ r → relu (c + β * r) - relu (d + δ * r) = r - 1)
    (hδ : δ < 0) : δ = -1 := by
  let R : ℝ := max 2 ((d + 1) / (-δ))
  have hR : 2 ≤ R := le_max_left _ _
  have hbound : d + 1 ≤ R * (-δ) :=
    (div_le_iff (neg_pos.mpr hδ)).mp (le_max_right _ _)
  have hdR : d + δ * R ≤ 0 := by nlinarith
  have hdR' : d + δ * (R + 1) ≤ 0 := by nlinarith
  have h0 := h R (by linarith)
  have h1 := h (R + 1) (by linarith)
  rw [relu_of_nonpos hdR, sub_zero] at h0
  rw [relu_of_nonpos hdR', sub_zero] at h1
  have hg0 : 0 < relu (c + β * R) := by rw [h0]; linarith
  have hg1 : 0 < relu (c + β * (R + 1)) := by rw [h1]; linarith
  rw [relu_eq_argument_of_pos hg0] at h0
  rw [relu_eq_argument_of_pos hg1] at h1
  have hβ : β = 1 := by nlinarith [h0, h1]
  have hc : c = -1 := by rw [hβ] at h0; linarith
  have hz := h 0 (by norm_num)
  simp only [mul_zero, add_zero, hc] at hz
  rw [relu_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)] at hz
  have hdpos : 0 < relu d := by linarith
  rw [relu_eq_argument_of_pos hdpos] at hz
  have hd : d = 1 := by linarith
  have hh := h (1 / 2) (by norm_num)
  rw [hc, hβ, hd] at hh
  norm_num only [one_mul] at hh
  rw [relu_of_nonpos (by norm_num : -(1 / 2 : ℝ) ≤ 0)] at hh
  have hhpos : 0 < relu (1 + δ * (1 / 2)) := by linarith
  rw [relu_eq_argument_of_pos hhpos] at hh
  linarith

/-- The coefficient gap used by signed versus split/hybrid base reconstructions.
`C,D` are unrestricted functions; no first-layer normal form is assumed here. -/
theorem base_slope_gap (C D : ℝ → ℝ → ℝ) (α β γ δ : ℝ)
    (h : ∀ a b q r : ℝ, 0 ≤ q → 0 ≤ r →
      relu (C a b + α * q + β * r) - relu (D a b + γ * q + δ * r) = b + r) :
    δ = -1 ∨ 0 ≤ δ := by
  rcases lt_or_ge δ 0 with hδ | hδ
  · left
    apply negative_base_slope_eq_neg_one (C 0 (-1)) (D 0 (-1)) β δ
    · intro r hr
      have hr' := h 0 (-1) 0 r (by norm_num) hr
      simp only [mul_zero, add_zero] at hr'
      convert hr' using 1 <;> ring
    · exact hδ
  · exact Or.inr hδ

/-- Inactive-region slack in the negative signed base neuron. -/
theorem signed_base_slack (b r c : ℝ) (hr : 0 ≤ r) (hc : c ≤ 1) :
    relu (-b - r + c * relu b) = relu (-b - r) := by
  rcases le_total b 0 with hb | hb
  · rw [relu_of_nonpos hb]
    simp
  · rw [relu_of_nonneg hb]
    rw [relu_of_nonpos (by nlinarith), relu_of_nonpos (by linarith)]

/-- The six fixed first-layer features of the ordinary paired Max4 code. -/
noncomputable def pairedFeatures (x : Point 4) : Fin 6 → ℝ :=
  ![relu (x 0 - x 1), relu (x 2 - x 3), relu (x 1), relu (-x 1),
    relu (x 3), relu (-x 3)]

theorem pairedFeatures_nonneg (x : Point 4) (j : Fin 6) :
    0 ≤ pairedFeatures x j := by
  fin_cases j <;> exact relu_nonneg _

private theorem paired_activation (x : Point 4) (j : Fin 6) :
    relu (∑ i, maxFourNet.W₁ j i * x i) = pairedFeatures x j := by
  fin_cases j <;>
    simp [maxFourNet, pairedFeatures, Fin.sum_univ_succ, sub_eq_add_neg] <;> rfl

private theorem pair_max_identity (a b : ℝ) :
    relu (a - b) + relu b - relu (-b) = max a b := by
  have h := relu_sub_add b a
  rw [max_comm] at h
  linarith [relu_sub_relu_neg b]

/-- The unique oriented comparison in these explicit families. This definition
does not assert uniqueness for arbitrary exact networks. -/
def pairedOuterCoefficients : Fin 6 → ℝ := ![1, -1, 1, -1, -1, 1]

private theorem paired_outer_sum (x : Point 4) :
    (∑ j, pairedOuterCoefficients j * pairedFeatures x j) =
      max (x 0) (x 1) - max (x 2) (x 3) := by
  norm_num [Fin.sum_univ_succ, pairedOuterCoefficients, pairedFeatures]
  linarith [pair_max_identity (x 0) (x 1), pair_max_identity (x 2) (x 3)]

/-- A network with the fixed paired first layer and two arbitrary base rows. -/
noncomputable def pairedNet (g h : Fin 6 → ℝ) : Network 4 6 3 where
  W₁ := maxFourNet.W₁
  b₁ := 0
  W₂ := ![g, h, pairedOuterCoefficients]
  b₂ := 0
  w₃ := ![1, -1, 1]
  b₃ := 0

theorem pairedNet_eval (g h : Fin 6 → ℝ) (x : Point 4) :
    (pairedNet g h).eval x =
      relu (∑ j, g j * pairedFeatures x j) -
      relu (∑ j, h j * pairedFeatures x j) +
      relu (max (x 0) (x 1) - max (x 2) (x 3)) := by
  unfold Network.eval pairedNet
  simp only [Pi.zero_apply, add_zero]
  simp_rw [paired_activation]
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, one_mul, neg_one_mul]
  rw [paired_outer_sum]
  ring

theorem pairedNet_eval_of_base (g h : Fin 6 → ℝ)
    (hbase : ∀ x : Point 4, relu (∑ j, g j * pairedFeatures x j) -
      relu (∑ j, h j * pairedFeatures x j) = max (x 2) (x 3)) :
    ∀ x, (pairedNet g h).eval x = Maximum 4 x := by
  intro x
  rw [pairedNet_eval, hbase x, Maximum_four]
  have e := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
  rw [max_comm (max (x 2) (x 3)) (max (x 0) (x 1))] at e
  linarith

/-- Exactness of this particular three-row presentation is equivalent to the
two designated base neurons reconstructing the selected pair maximum. -/
theorem pairedNet_exact_iff_base (g h : Fin 6 → ℝ) :
    (∀ x, (pairedNet g h).eval x = Maximum 4 x) ↔
      ∀ x : Point 4, relu (∑ j, g j * pairedFeatures x j) -
        relu (∑ j, h j * pairedFeatures x j) = max (x 2) (x 3) := by
  constructor
  · intro he x
    have hx := he x
    rw [pairedNet_eval, Maximum_four] at hx
    have e := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
    rw [max_comm (max (x 2) (x 3)) (max (x 0) (x 1))] at e
    linarith
  · exact pairedNet_eval_of_base g h

/-- An actual exact-network coefficient gap in the fixed paired first-layer,
fixed comparison-row slice. The full fiber classification is a separate step. -/
theorem pairedNet_negative_base_coefficient_gap (g h : Fin 6 → ℝ)
    (he : ∀ x, (pairedNet g h).eval x = Maximum 4 x) :
    h 1 = -1 ∨ 0 ≤ h 1 := by
  rcases lt_or_ge (h 1) 0 with hneg | hnn
  · left
    apply negative_base_slope_eq_neg_one (g 5) (h 5) (g 1) (h 1)
    · intro r hr
      have e := (pairedNet_exact_iff_base g h).mp he ![0, 0, r - 1, -1]
      have er : r - 1 - (-1) = r := by ring
      have em : max (r - 1) (-1) = r - 1 := max_eq_left (by linarith)
      norm_num [Fin.sum_univ_succ, pairedFeatures] at e
      have elast : (![0, 0, r - 1, -1] : Point 4) 3 = -1 := rfl
      rw [elast] at e
      rw [er, relu_of_nonneg hr, em] at e
      norm_num [relu] at e
      change relu (g 1 * r + g 5) - relu (h 1 * r + h 5) = r - 1 at e
      rw [add_comm (g 1 * r) (g 5), add_comm (h 1 * r) (h 5)] at e
      exact e
    · exact hneg
  · exact Or.inr hnn

/-- Signed base reconstruction with every allowable slack coefficient in this
fixed aligned code. The output function is proved below for all real inputs. -/
noncomputable def signedSlackNet (c : ℝ) : Network 4 6 3 :=
  pairedNet ![0, 1, 0, 0, 1, -1] ![0, -1, 0, 0, c - 1, 1]

/-- The common-mode split family. Nonnegative `z` preserves exactness. -/
noncomputable def splitNet (z : Fin 6 → ℝ) : Network 4 6 3 :=
  pairedNet (fun j => (![0, 1, 0, 0, 1, 0] : Fin 6 → ℝ) j + z j)
    (fun j => (![0, 0, 0, 0, 0, 1] : Fin 6 → ℝ) j + z j)

/-- The aligned-code hybrid family. Its boundary at `μ = 0` is in the split
family, while the entire family has zero selected-root coefficient in its
negative base neuron. -/
noncomputable def hybridNet (ell μ : ℝ) : Network 4 6 3 :=
  pairedNet ![0, 1, 0, 0, 1, ell - 1] ![0, 0, 0, 0, μ, ell]

theorem signedSlackNet_eval (c : ℝ) (hc : c ≤ 1) :
    ∀ x, (signedSlackNet c).eval x = Maximum 4 x := by
  apply pairedNet_eval_of_base
  intro x
  norm_num [Fin.sum_univ_succ, pairedFeatures]
  have eb := relu_sub_relu_neg (x 3)
  have e1 : relu (x 2 - x 3) + relu (x 3) - relu (-x 3) =
      max (x 2) (x 3) := pair_max_identity _ _
  have e2 : -relu (x 2 - x 3) + ((c - 1) * relu (x 3) + relu (-x 3)) =
      -x 3 - relu (x 2 - x 3) + c * relu (x 3) := by nlinarith
  rw [e2, signed_base_slack _ _ _ (relu_nonneg _) hc]
  have e3 : -x 3 - relu (x 2 - x 3) = -max (x 2) (x 3) := by linarith
  rw [e3]
  have e4 : relu (x 2 - x 3) + (relu (x 3) + -relu (-x 3)) =
      max (x 2) (x 3) := by linarith
  rw [e4]
  exact relu_sub_relu_neg _

theorem splitNet_eval (z : Fin 6 → ℝ) (hz : ∀ j, 0 ≤ z j) :
    ∀ x, (splitNet z).eval x = Maximum 4 x := by
  apply pairedNet_eval_of_base
  intro x
  have hcommon : 0 ≤ ∑ j, z j * pairedFeatures x j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hz j) (pairedFeatures_nonneg x j)
  have hp : (∑ j, (![0, 1, 0, 0, 1, 0] : Fin 6 → ℝ) j * pairedFeatures x j) =
      relu (x 2 - x 3) + relu (x 3) := by
    norm_num [Fin.sum_univ_succ, pairedFeatures]
  have hn : (∑ j, (![0, 0, 0, 0, 0, 1] : Fin 6 → ℝ) j * pairedFeatures x j) =
      relu (-x 3) := by
    norm_num [Fin.sum_univ_succ, pairedFeatures]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hp, hn]
  rw [relu_of_nonneg (add_nonneg (add_nonneg (relu_nonneg _) (relu_nonneg _)) hcommon),
    relu_of_nonneg (add_nonneg (relu_nonneg _) hcommon)]
  linarith [pair_max_identity (x 2) (x 3)]

theorem hybridNet_eval (ell μ : ℝ) (hell : 1 ≤ ell) (hμ : μ ≤ 0) :
    ∀ x, (hybridNet ell μ).eval x = Maximum 4 x := by
  apply pairedNet_eval_of_base
  intro x
  norm_num [Fin.sum_univ_succ, pairedFeatures]
  have hpos : 0 ≤ relu (x 2 - x 3) + (relu (x 3) + (ell - 1) * relu (-x 3)) := by
    exact add_nonneg (relu_nonneg _)
      (add_nonneg (relu_nonneg _) (mul_nonneg (by linarith) (relu_nonneg _)))
  rw [relu_of_nonneg hpos]
  rcases le_total (x 3) 0 with hb | hb
  · have hb' : 0 ≤ -x 3 := by linarith
    simp only [relu_of_nonpos hb, relu_of_nonneg hb', mul_zero, zero_mul,
      zero_add, add_zero]
    rw [relu_of_nonneg (mul_nonneg (show 0 ≤ ell by linarith) hb')]
    have e := pair_max_identity (x 2) (x 3)
    rw [relu_of_nonpos hb, relu_of_nonneg hb'] at e
    nlinarith
  · have hb' : -x 3 ≤ 0 := by linarith
    simp only [relu_of_nonneg hb, relu_of_nonpos hb', mul_zero, zero_mul,
      add_zero, zero_add]
    rw [relu_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hμ hb)]
    have e := pair_max_identity (x 2) (x 3)
    rw [relu_of_nonneg hb, relu_of_nonpos hb'] at e
    linarith

end Fiber
end MaxCaterpillar
