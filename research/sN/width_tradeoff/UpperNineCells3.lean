import research.sN.width_tradeoff.UpperNineDefs
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.WidthTradeoff.P4
open BigOperators MaxCaterpillar.SmallN
open MaxNN.Caterpillar.Corrections

theorem chamber90 (x : Point 5) (h0 : x 4 ≤ x 3) (h1 : x 0 ≤ x 4) (h2 : x 1 ≤ x 0) (h3 : x 2 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (1) * (x 3) + (-1) * (x 4) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((1) * (x 3) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 0) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 3 := max_eq x 3 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber91 (x : Point 5) (h0 : x 4 ≤ x 3) (h1 : x 0 ≤ x 4) (h2 : x 2 ≤ x 0) (h3 : x 1 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
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
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 0) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 3 := max_eq x 3 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber92 (x : Point 5) (h0 : x 4 ≤ x 3) (h1 : x 1 ≤ x 4) (h2 : x 0 ≤ x 1) (h3 : x 2 ≤ x 0) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (1) * (x 3) + (-1) * (x 4) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((1) * (x 3) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 3 := max_eq x 3 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber93 (x : Point 5) (h0 : x 4 ≤ x 3) (h1 : x 1 ≤ x 4) (h2 : x 2 ≤ x 1) (h3 : x 0 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (1) * (x 3) + (-1) * (x 4) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((1) * (x 3) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 3 := max_eq x 3 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber94 (x : Point 5) (h0 : x 4 ≤ x 3) (h1 : x 2 ≤ x 4) (h2 : x 0 ≤ x 2) (h3 : x 1 ≤ x 0) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
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
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 0) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 3 := max_eq x 3 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber95 (x : Point 5) (h0 : x 4 ≤ x 3) (h1 : x 2 ≤ x 4) (h2 : x 1 ≤ x 2) (h3 : x 0 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = x 3 - x 4 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (1) * (x 3) + (-1) * (x 4) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((1) * (x 3) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) + ((1/2 : ℝ)) * (x 3) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 3 := max_eq x 3 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber96 (x : Point 5) (h0 : x 0 ≤ x 4) (h1 : x 1 ≤ x 0) (h2 : x 2 ≤ x 1) (h3 : x 3 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
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
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber97 (x : Point 5) (h0 : x 0 ≤ x 4) (h1 : x 1 ≤ x 0) (h2 : x 3 ≤ x 1) (h3 : x 2 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
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
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber98 (x : Point 5) (h0 : x 0 ≤ x 4) (h1 : x 2 ≤ x 0) (h2 : x 1 ≤ x 2) (h3 : x 3 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
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
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber99 (x : Point 5) (h0 : x 0 ≤ x 4) (h1 : x 2 ≤ x 0) (h2 : x 3 ≤ x 2) (h3 : x 1 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
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
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber100 (x : Point 5) (h0 : x 0 ≤ x 4) (h1 : x 3 ≤ x 0) (h2 : x 1 ≤ x 3) (h3 : x 2 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
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
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber101 (x : Point 5) (h0 : x 0 ≤ x 4) (h1 : x 3 ≤ x 0) (h2 : x 2 ≤ x 3) (h3 : x 1 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
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
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber102 (x : Point 5) (h0 : x 1 ≤ x 4) (h1 : x 0 ≤ x 1) (h2 : x 2 ≤ x 0) (h3 : x 3 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
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
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber103 (x : Point 5) (h0 : x 1 ≤ x 4) (h1 : x 0 ≤ x 1) (h2 : x 3 ≤ x 0) (h3 : x 2 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
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
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber104 (x : Point 5) (h0 : x 1 ≤ x 4) (h1 : x 2 ≤ x 1) (h2 : x 0 ≤ x 2) (h3 : x 3 ≤ x 0) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
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
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber105 (x : Point 5) (h0 : x 1 ≤ x 4) (h1 : x 2 ≤ x 1) (h2 : x 3 ≤ x 2) (h3 : x 0 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
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
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (1) * (x 1) + (-1) * (x 3) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber106 (x : Point 5) (h0 : x 1 ≤ x 4) (h1 : x 3 ≤ x 1) (h2 : x 0 ≤ x 3) (h3 : x 2 ≤ x 0) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
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
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (1) * (x 1) + (-1) * (x 3) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber107 (x : Point 5) (h0 : x 1 ≤ x 4) (h1 : x 3 ≤ x 1) (h2 : x 2 ≤ x 3) (h3 : x 0 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
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
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (1) * (x 1) + (-1) * (x 3) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber108 (x : Point 5) (h0 : x 2 ≤ x 4) (h1 : x 0 ≤ x 2) (h2 : x 1 ≤ x 0) (h3 : x 3 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
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
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber109 (x : Point 5) (h0 : x 2 ≤ x 4) (h1 : x 0 ≤ x 2) (h2 : x 3 ≤ x 0) (h3 : x 1 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
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
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber110 (x : Point 5) (h0 : x 2 ≤ x 4) (h1 : x 1 ≤ x 2) (h2 : x 0 ≤ x 1) (h3 : x 3 ≤ x 0) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (-1) * (x 0) + (1) * (x 1) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((-1) * (x 0) + (1) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber111 (x : Point 5) (h0 : x 2 ≤ x 4) (h1 : x 1 ≤ x 2) (h2 : x 3 ≤ x 1) (h3 : x 0 ≤ x 3) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = (1) * (x 1) + (-1) * (x 3) := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber112 (x : Point 5) (h0 : x 2 ≤ x 4) (h1 : x 3 ≤ x 2) (h2 : x 0 ≤ x 3) (h3 : x 1 ≤ x 0) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
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
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 0) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber113 (x : Point 5) (h0 : x 2 ≤ x 4) (h1 : x 3 ≤ x 2) (h2 : x 1 ≤ x 3) (h3 : x 0 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber114 (x : Point 5) (h0 : x 3 ≤ x 4) (h1 : x 0 ≤ x 3) (h2 : x 1 ≤ x 0) (h3 : x 2 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 0) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber115 (x : Point 5) (h0 : x 3 ≤ x 4) (h1 : x 0 ≤ x 3) (h2 : x 2 ≤ x 0) (h3 : x 1 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
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
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 0) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber116 (x : Point 5) (h0 : x 3 ≤ x 4) (h1 : x 1 ≤ x 3) (h2 : x 0 ≤ x 1) (h3 : x 2 ≤ x 0) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber117 (x : Point 5) (h0 : x 3 ≤ x 4) (h1 : x 1 ≤ x 3) (h2 : x 2 ≤ x 1) (h3 : x 0 ≤ x 2) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 1)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber118 (x : Point 5) (h0 : x 3 ≤ x 4) (h1 : x 2 ≤ x 3) (h2 : x 0 ≤ x 2) (h3 : x 1 ≤ x 0) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
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
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 0) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 0) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 0) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

theorem chamber119 (x : Point 5) (h0 : x 3 ≤ x 4) (h1 : x 2 ≤ x 3) (h2 : x 1 ≤ x 2) (h3 : x 0 ≤ x 1) : Maximum 5 x = rhs x := by
  have f0 : relu (x 1 - x 0) = x 1 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f1 : relu (x 2 - x 0) = x 2 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f2 : relu (x 2 - x 1) = x 2 - x 1 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f3 : relu (x 3 - x 0) = x 3 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f4 : relu (x 4 - x 0) = x 4 - x 0 := relu_eq_self (by linarith only [h0,h1,h2,h3])
  have f5 : relu (x 3 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have f6 : relu (x 2 - x 4) = 0 := relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o0 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o1 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o2 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o3 : relu ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = (0 : ℝ) := by
    rw [show ((1) * (relu (x 3 - x 4)) + (-1) * (relu (x 2 - x 4))) = ((0 : ℝ)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o4 : relu (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 1)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 1) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o5 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o6 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 2 - x 1)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o7 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((-1/2 : ℝ)) * (relu (x 4 - x 0))) = (((1/2 : ℝ)) * (x 2) + ((-1/2 : ℝ)) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o8 : relu (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = ((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2) := by
    rw [show (((1/2 : ℝ)) * (relu (x 2 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4)) + ((-1/2 : ℝ)) * (relu (x 2 - x 4))) = (((-1/2 : ℝ)) * (x 0) + ((1/2 : ℝ)) * (x 2)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_self (by linarith only [h0,h1,h2,h3])
  have o9 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 3 - x 0))) = ((1) * (x 1) + (-1) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o10 : relu (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = 0 := by
    rw [show (((1/2 : ℝ)) * (relu (x 1 - x 0)) + ((-1/2 : ℝ)) * (relu (x 3 - x 0)) + ((1/2 : ℝ)) * (relu (x 3 - x 4))) = (((1/2 : ℝ)) * (x 1) + ((-1/2 : ℝ)) * (x 3)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have o11 : relu ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = 0 := by
    rw [show ((1) * (relu (x 1 - x 0)) + (-1) * (relu (x 4 - x 0))) = ((1) * (x 1) + (-1) * (x 4)) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]
    exact relu_eq_zero (by linarith only [h0,h1,h2,h3])
  have hm : Maximum 5 x = x 4 := max_eq x 4 (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3]) (by linarith only [h0,h1,h2,h3])
  rw [hm]
  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]
  simp only [f0,f1,f2,f3,f4,f5,f6]
  ring

end MaxCaterpillar.WidthTradeoff.P4
