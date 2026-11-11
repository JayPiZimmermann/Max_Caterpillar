import research.sN.frontierN.overnight_general_antipodal

/-! Exact ordinary-network baseline for the Max5 optimal-width search.
This specializes an existing theorem; it is not a new numerical lower bound.
The `Network` type has arbitrary real biases and no skip connections. -/
set_option autoImplicit false

namespace MaxCaterpillar.Max5Optimal.Lower

open BigOperators Frontier

theorem second_width_ge_four {h₁ h₂ : ℕ} (net : Network 5 h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum 5 x) : 4 ≤ h₂ := by
  have h := OvernightGeneral.network_second_width_half_plus_one net hnet
  by_contra hn
  have hle : h₂ ≤ 3 := Nat.le_of_lt_succ (lt_of_not_ge hn)
  have ht : 2*h₂ ≤ 6 := Nat.mul_le_mul_left 2 hle
  norm_num at h
  linarith only [h,ht]

theorem no_second_width_three (h₁ : ℕ) :
    ¬ ∃ net : Network 5 h₁ 3, ∀ x, net.eval x = Maximum 5 x := by
  rintro ⟨net,hnet⟩
  have h := second_width_ge_four net hnet
  omega

/-- Literal ordinary architecture, including both hidden biases and output bias. -/
theorem second_width_ge_four_raw {h₁ h₂ : ℕ}
    (A : Fin h₁ → Fin 5 → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (c : Fin h₂ → ℝ)
    (d : Fin h₂ → ℝ) (e : ℝ)
    (hnet : ∀ x : Fin 5 → ℝ,
      (∑ k, d k * max 0 ((∑ j, W k j * max 0
        ((∑ i, A j i * x i) + b j)) + c k)) + e = Maximum 5 x) : 4 ≤ h₂ := by
  let net : Network 5 h₁ h₂ := ⟨A,b,W,c,d,e⟩
  exact second_width_ge_four net hnet

#check @second_width_ge_four
#check @no_second_width_three
#check @second_width_ge_four_raw
#print axioms second_width_ge_four
#print axioms no_second_width_three
#print axioms second_width_ge_four_raw

end MaxCaterpillar.Max5Optimal.Lower
