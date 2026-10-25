import MaxCaterpillar.SmallN.Common
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.WidthTradeoff.P4
open BigOperators MaxCaterpillar.SmallN
open MaxNN.Caterpillar.Corrections
noncomputable def rhs (x : Point 5) : ℝ :=
    (1) * relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) +
    (-1) * relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) +
    (1) * relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) +
    (1) * relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) +
    (-1) * relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) +
    (-1) * relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) +
    (-1) * relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) +
    (1) * relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) +
    (-1) * relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) +
    (1) * relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) +
    (-1) * relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) +
    (1) * relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) +
    x 0 + ((-1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 0)) + (1) * (relu (x 4 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))


theorem max_eq (x : Point 5) (t : Fin 5)
    (h0 : x 0 ≤ x t) (h1 : x 1 ≤ x t) (h2 : x 2 ≤ x t)
    (h3 : x 3 ≤ x t) (h4 : x 4 ≤ x t) : Maximum 5 x = x t := by
  apply maximum_eq_of_le x t
  intro i
  fin_cases i
  exacts [h0,h1,h2,h3,h4]

theorem relu_scale (c u : ℝ) (hc : 0 ≤ c) : relu (c*u) = c*relu u := by
  unfold relu
  rcases le_total 0 u with h | h
  · rw [max_eq_right h, max_eq_right (mul_nonneg hc h)]
  · rw [max_eq_left h, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc h), mul_zero]

theorem relu_scale_neg (c u : ℝ) (hc : 0 ≤ c) :
    relu (-(c*u)) = c*relu u - c*u := by
  have h := relu_sub_relu_neg_self (c*u)
  rw [relu_scale c u hc] at h
  linarith
end MaxCaterpillar.WidthTradeoff.P4
