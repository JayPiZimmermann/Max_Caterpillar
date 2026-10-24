import Mathlib

/-! Restricted-model germ identity (research/sN/restricted).
The neuron `relu (Σ_Q relu(x_q - x_a) - Σ_P relu(x_p - x_a))` has, at a top
3-tie `{a, p, q}`, the germ `relu (relu (q - a) - relu (p - a))`, which equals
`max a (max p q) - max a p`: a genuine `max₃` term (outside the hinge span).
This is the identity behind the per-neuron capacity `|P||Q|(N-3)!`. -/

theorem germ_max3 (a p q : ℝ) :
    max (max (q - a) 0 - max (p - a) 0) 0 = max a (max p q) - max a p := by
  rcases le_total a p with h1 | h1 <;> rcases le_total a q with h2 | h2 <;>
    rcases le_total p q with h3 | h3 <;>
    simp only [max_def] <;> split_ifs <;> linarith
