import MaxCaterpillar.Frontier.FirstWidth

/-!
A uniform first-hidden-layer consequence of the already checked Lemma M.
No finite certificate, sampled search, coefficient restriction, or bias restriction is used.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier

variable {N h₁ h₂ : ℕ}

/-- For four or more inputs, `N + 1` first neurons are impossible, regardless of
    the width of the second hidden layer. -/
theorem ZNet.first_width_ge_add_two [NeZero N] (hN : 4 ≤ N)
    (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) : N + 2 ≤ h₁ := by
  by_contra hlt
  push_neg at hlt
  have a1 := net.card_nonneg h
  have a2 := net.card_nonpos h
  obtain ⟨j, hj⟩ := net.exists_neg h
  obtain ⟨j', hj'⟩ := net.exists_pos h
  have a3 : 1 ≤ (Finset.univ.filter fun j => net.s j < 0).card :=
    Finset.card_pos.2 ⟨j, by simp [hj]⟩
  have a4 : 1 ≤ (Finset.univ.filter fun j => 0 < net.s j).card :=
    Finset.card_pos.2 ⟨j', by simp [hj']⟩
  have b1 := card_filter_split net.s
  have b2 := card_filter_split' net.s
  rw [Fintype.card_fin] at b1 b2
  exact net.lemmaM hN h (le_antisymm (by omega) a4) (le_antisymm (by omega) a1)

/-- The same bound for the actual network model, including arbitrary real biases. -/
theorem first_width_ge_add_two [NeZero N] (hN : 4 ≤ N)
    (net : Network N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) : N + 2 ≤ h₁ :=
  net.toZ.first_width_ge_add_two hN (net.toZ_eval_of_max h)

/-- In particular, the first hidden layer for max-five has width at least seven. -/
theorem first_width_ge_seven_max5 (net : Network 5 h₁ h₂)
    (h : ∀ x, net.eval x = Maximum 5 x) : 7 ≤ h₁ :=
  first_width_ge_add_two (by decide) net h

#check @first_width_ge_add_two
#check @first_width_ge_seven_max5
#print axioms first_width_ge_add_two
#print axioms first_width_ge_seven_max5

end MaxCaterpillar.Frontier
