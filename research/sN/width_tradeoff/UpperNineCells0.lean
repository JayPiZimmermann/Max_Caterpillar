import research.sN.width_tradeoff.UpperNineDefs
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.WidthTradeoff.P4
open BigOperators MaxCaterpillar.SmallN
open MaxNN.Caterpillar.Corrections

theorem chamber0 (x : Point 5) (h0 : x 1 ≤ x 0) (h1 : x 2 ≤ x 1) (h2 : x 3 ≤ x 2) (h3 : x 4 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = 0 := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber1 (x : Point 5) (h0 : x 1 ≤ x 0) (h1 : x 2 ≤ x 1) (h2 : x 4 ≤ x 2) (h3 : x 3 ≤ x 4) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = 0 := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber2 (x : Point 5) (h0 : x 1 ≤ x 0) (h1 : x 3 ≤ x 1) (h2 : x 2 ≤ x 3) (h3 : x 4 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (-1) * (x 2) + (1) * (x 3) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber3 (x : Point 5) (h0 : x 1 ≤ x 0) (h1 : x 3 ≤ x 1) (h2 : x 4 ≤ x 3) (h3 : x 2 ≤ x 4) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (1) * (x 3) + (-1) * (x 4) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((1) * (x 3) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber4 (x : Point 5) (h0 : x 1 ≤ x 0) (h1 : x 4 ≤ x 1) (h2 : x 2 ≤ x 4) (h3 : x 3 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber5 (x : Point 5) (h0 : x 1 ≤ x 0) (h1 : x 4 ≤ x 1) (h2 : x 3 ≤ x 4) (h3 : x 2 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber6 (x : Point 5) (h0 : x 2 ≤ x 0) (h1 : x 1 ≤ x 2) (h2 : x 3 ≤ x 1) (h3 : x 4 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + (-1) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = 0 := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber7 (x : Point 5) (h0 : x 2 ≤ x 0) (h1 : x 1 ≤ x 2) (h2 : x 4 ≤ x 1) (h3 : x 3 ≤ x 4) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + (-1) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = 0 := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber8 (x : Point 5) (h0 : x 2 ≤ x 0) (h1 : x 3 ≤ x 2) (h2 : x 1 ≤ x 3) (h3 : x 4 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + (-1) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = 0 := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber9 (x : Point 5) (h0 : x 2 ≤ x 0) (h1 : x 3 ≤ x 2) (h2 : x 4 ≤ x 3) (h3 : x 1 ≤ x 4) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + (-1) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = 0 := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber10 (x : Point 5) (h0 : x 2 ≤ x 0) (h1 : x 4 ≤ x 2) (h2 : x 1 ≤ x 4) (h3 : x 3 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + (-1) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = 0 := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber11 (x : Point 5) (h0 : x 2 ≤ x 0) (h1 : x 4 ≤ x 2) (h2 : x 3 ≤ x 4) (h3 : x 1 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + (-1) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = 0 := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber12 (x : Point 5) (h0 : x 3 ≤ x 0) (h1 : x 1 ≤ x 3) (h2 : x 2 ≤ x 1) (h3 : x 4 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (-1) * (x 2) + (1) * (x 3) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber13 (x : Point 5) (h0 : x 3 ≤ x 0) (h1 : x 1 ≤ x 3) (h2 : x 4 ≤ x 1) (h3 : x 2 ≤ x 4) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (1) * (x 3) + (-1) * (x 4) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((1) * (x 3) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber14 (x : Point 5) (h0 : x 3 ≤ x 0) (h1 : x 2 ≤ x 3) (h2 : x 1 ≤ x 2) (h3 : x 4 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + (-1) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (-1) * (x 2) + (1) * (x 3) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber15 (x : Point 5) (h0 : x 3 ≤ x 0) (h1 : x 2 ≤ x 3) (h2 : x 4 ≤ x 2) (h3 : x 1 ≤ x 4) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + (-1) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (-1) * (x 2) + (1) * (x 3) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber16 (x : Point 5) (h0 : x 3 ≤ x 0) (h1 : x 4 ≤ x 3) (h2 : x 1 ≤ x 4) (h3 : x 2 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (1) * (x 3) + (-1) * (x 4) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((1) * (x 3) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber17 (x : Point 5) (h0 : x 3 ≤ x 0) (h1 : x 4 ≤ x 3) (h2 : x 2 ≤ x 4) (h3 : x 1 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (1) * (x 3) + (-1) * (x 4) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((1) * (x 3) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber18 (x : Point 5) (h0 : x 4 ≤ x 0) (h1 : x 1 ≤ x 4) (h2 : x 2 ≤ x 1) (h3 : x 3 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber19 (x : Point 5) (h0 : x 4 ≤ x 0) (h1 : x 1 ≤ x 4) (h2 : x 3 ≤ x 1) (h3 : x 2 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber20 (x : Point 5) (h0 : x 4 ≤ x 0) (h1 : x 2 ≤ x 4) (h2 : x 1 ≤ x 2) (h3 : x 3 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber21 (x : Point 5) (h0 : x 4 ≤ x 0) (h1 : x 2 ≤ x 4) (h2 : x 3 ≤ x 2) (h3 : x 1 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber22 (x : Point 5) (h0 : x 4 ≤ x 0) (h1 : x 3 ≤ x 4) (h2 : x 1 ≤ x 3) (h3 : x 2 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber23 (x : Point 5) (h0 : x 4 ≤ x 0) (h1 : x 3 ≤ x 4) (h2 : x 2 ≤ x 3) (h3 : x 1 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 0 := max_eq x 0 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber24 (x : Point 5) (h0 : x 0 ≤ x 1) (h1 : x 2 ≤ x 0) (h2 : x 3 ≤ x 2) (h3 : x 4 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * relu ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 3)) - ((1/2 : ℝ)) * ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 3)) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (-(((1/2 : ℝ)) * ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 3)))) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_scale_neg ((1/2 : ℝ)) ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 3)) (by norm_num)
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * relu ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 3)) - ((1/2 : ℝ)) * ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 3)) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (-(((1/2 : ℝ)) * ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 3)))) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_scale_neg ((1/2 : ℝ)) ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 3)) (by norm_num)
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = 0 := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 1 := max_eq x 1 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber25 (x : Point 5) (h0 : x 0 ≤ x 1) (h1 : x 2 ≤ x 0) (h2 : x 4 ≤ x 2) (h3 : x 3 ≤ x 4) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * relu ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 4)) - ((1/2 : ℝ)) * ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 4)) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (-(((1/2 : ℝ)) * ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 4)))) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_scale_neg ((1/2 : ℝ)) ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 4)) (by norm_num)
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * relu ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 4)) - ((1/2 : ℝ)) * ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 4)) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (-(((1/2 : ℝ)) * ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 4)))) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_scale_neg ((1/2 : ℝ)) ((1) * (x 0) + (-1) * (x 1) + (1) * (x 2) + (-1) * (x 4)) (by norm_num)
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = 0 := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 1 := max_eq x 1 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber26 (x : Point 5) (h0 : x 0 ≤ x 1) (h1 : x 3 ≤ x 0) (h2 : x 2 ≤ x 3) (h3 : x 4 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = x 2 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (-1) * (x 2) + (1) * (x 3) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((-1) * (x 2) + (1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 1 := max_eq x 1 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber27 (x : Point 5) (h0 : x 0 ≤ x 1) (h1 : x 3 ≤ x 0) (h2 : x 4 ≤ x 3) (h3 : x 2 ≤ x 4) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (1) * (x 3) + (-1) * (x 4) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((1) * (x 3) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 1 := max_eq x 1 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber28 (x : Point 5) (h0 : x 0 ≤ x 1) (h1 : x 4 ≤ x 0) (h2 : x 2 ≤ x 4) (h3 : x 3 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 1 := max_eq x 1 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber29 (x : Point 5) (h0 : x 0 ≤ x 1) (h1 : x 4 ≤ x 0) (h2 : x 3 ≤ x 4) (h3 : x 2 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 1 := max_eq x 1 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

end MaxCaterpillar.WidthTradeoff.P4
