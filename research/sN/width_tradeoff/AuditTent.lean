import MaxCaterpillar.Frontier.Main

/-!
A strict width tradeoff for a one-dimensional CPWL target, in the actual
two-hidden-layer `Network` model with arbitrary biases and no skips.
This is a counterexample to a generic simultaneous-minimum principle.
It does not decide the frontier of `Maximum N` for N >= 5.
-/

namespace MaxCaterpillar.Frontier.WidthTradeoffAudit

open BigOperators

noncomputable def tent (t : ℝ) : ℝ :=
  relu t - 2 * relu (t - 1) + relu (t - 2)

noncomputable def tent12 : Network 1 1 2 where
  W₁ := ![![1]]
  b₁ := 0
  W₂ := ![![-1], ![-1]]
  b₂ := ![2, 1]
  w₃ := ![1, -2]
  b₃ := 0

noncomputable def tent21 : Network 1 2 1 where
  W₁ := ![![1], ![1]]
  b₁ := ![0, -1]
  W₂ := ![![1, -2]]
  b₂ := 0
  w₃ := ![1]
  b₃ := 0

lemma tent21_eval (x : Point 1) : tent21.eval x = tent (x 0) := by
  simp only [Network.eval, tent21, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply]
  simp only [one_mul, zero_mul, neg_mul, add_zero, zero_add, Fin.succ_zero_eq_one]
  simp only [tent, relu, max_def]
  split_ifs <;> linarith

lemma tent12_eval (x : Point 1) : tent12.eval x = tent (x 0) := by
  simp only [Network.eval, tent12, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply]
  simp only [one_mul, zero_mul, neg_mul, add_zero, zero_add, Fin.succ_zero_eq_one]
  simp only [tent, relu, max_def]
  split_ifs <;> linarith

lemma affine_mono_or_anti (a b : ℝ) :
    Monotone (fun x : ℝ => a * x + b) ∨ Antitone (fun x : ℝ => a * x + b) := by
  rcases le_total 0 a with ha | ha
  · left
    intro x y hxy
    exact add_le_add_right (mul_le_mul_of_nonneg_left hxy ha) b
  · right
    intro x y hxy
    exact add_le_add_right (mul_le_mul_of_nonpos_left hxy ha) b

lemma mono_or_anti_comp {f g : ℝ → ℝ}
    (hf : Monotone f ∨ Antitone f) (hg : Monotone g ∨ Antitone g) :
    Monotone (f ∘ g) ∨ Antitone (f ∘ g) := by
  rcases hf with hf | hf <;> rcases hg with hg | hg
  · exact Or.inl fun _ _ h => hf (hg h)
  · exact Or.inr fun _ _ h => hf (hg h)
  · exact Or.inr fun _ _ h => hf (hg h)
  · exact Or.inl fun _ _ h => hf (hg h)

lemma scalar_layer_mono_or_anti (a b : ℝ) :
    Monotone (fun x : ℝ => relu (a * x + b)) ∨
      Antitone (fun x : ℝ => relu (a * x + b)) := by
  exact mono_or_anti_comp
    (Or.inl (fun _ _ h => max_le_max le_rfl h)) (affine_mono_or_anti a b)

/-- A network with one scalar neuron in each hidden layer is monotone or antitone,
even with arbitrary weights and all biases. -/
theorem network11_mono_or_anti (net : Network 1 1 1) :
    Monotone (fun t : ℝ => net.eval (fun _ => t)) ∨
      Antitone (fun t : ℝ => net.eval (fun _ => t)) := by
  have h := mono_or_anti_comp (affine_mono_or_anti (net.w₃ 0) net.b₃)
    (mono_or_anti_comp (scalar_layer_mono_or_anti (net.W₂ 0 0) (net.b₂ 0))
      (scalar_layer_mono_or_anti (net.W₁ 0 0) (net.b₁ 0)))
  simpa only [Function.comp_apply, Network.eval, Fin.sum_univ_one] using h

theorem no_tent11 (net : Network 1 1 1) :
    ¬ (∀ x, net.eval x = tent (x 0)) := by
  intro h
  rcases network11_mono_or_anti net with hm | hm
  · have hi := hm (show (1 : ℝ) ≤ 2 by norm_num)
    dsimp only at hi
    rw [h, h] at hi
    norm_num [tent, relu] at hi
  · have hi := hm (show (0 : ℝ) ≤ 1 by norm_num)
    dsimp only at hi
    rw [h, h] at hi
    norm_num [tent, relu] at hi

theorem no_tent_zero_second {m : ℕ} (net : Network 1 m 0) :
    ¬ (∀ x, net.eval x = tent (x 0)) := by
  intro h
  have h0 := h (fun _ => 0)
  have h1 := h (fun _ => 1)
  norm_num [Network.eval, tent, relu] at h0 h1
  linarith

theorem no_tent_zero_first {n : ℕ} (net : Network 1 0 n) :
    ¬ (∀ x, net.eval x = tent (x 0)) := by
  intro h
  have h0 := h (fun _ => 0)
  have h1 := h (fun _ => 1)
  norm_num [Network.eval, tent, relu] at h0 h1
  linarith

/-- Both coordinatewise minima are one, and they cannot be attained together. -/
theorem tent_width_tradeoff :
    (∃ net : Network 1 1 2, ∀ x, net.eval x = tent (x 0)) ∧
    (∃ net : Network 1 2 1, ∀ x, net.eval x = tent (x 0)) ∧
    ¬ (∃ net : Network 1 1 1, ∀ x, net.eval x = tent (x 0)) := by
  exact ⟨⟨tent12, tent12_eval⟩, ⟨tent21, tent21_eval⟩,
    fun ⟨net, h⟩ => no_tent11 net h⟩

/-- The full width frontier has exactly two incomparable points: `(1,2)` and `(2,1)`. -/
theorem tent_widths_iff {a b : ℕ} :
    (∃ net : Network 1 a b, ∀ x, net.eval x = tent (x 0)) ↔
      (1 ≤ a ∧ 2 ≤ b) ∨ (2 ≤ a ∧ 1 ≤ b) := by
  constructor
  · rintro ⟨net, h⟩
    have ha : a ≠ 0 := by
      intro he
      subst a
      exact no_tent_zero_first net h
    have hb : b ≠ 0 := by
      intro he
      subst b
      exact no_tent_zero_second net h
    have hab : ¬ (a = 1 ∧ b = 1) := by
      rintro ⟨rfl, rfl⟩
      exact no_tent11 net h
    by_cases ha1 : a = 1
    · have hb1 : b ≠ 1 := fun hb1 => hab ⟨ha1, hb1⟩
      exact Or.inl ⟨Nat.one_le_iff_ne_zero.2 ha, (Nat.two_le_iff b).2 ⟨hb, hb1⟩⟩
    · exact Or.inr ⟨(Nat.two_le_iff a).2 ⟨ha, ha1⟩, Nat.one_le_iff_ne_zero.2 hb⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact exists_network_of_le tent12 tent12_eval ha hb
    · exact exists_network_of_le tent21 tent21_eval ha hb

theorem tent_first_one_iff {b : ℕ} :
    (∃ net : Network 1 1 b, ∀ x, net.eval x = tent (x 0)) ↔ 2 ≤ b := by
  rw [tent_widths_iff]
  norm_num

theorem tent_first_two_iff {b : ℕ} :
    (∃ net : Network 1 2 b, ∀ x, net.eval x = tent (x 0)) ↔ 1 ≤ b := by
  rw [tent_widths_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> omega
  · intro h
    exact Or.inr ⟨le_refl 2, h⟩

#print axioms network11_mono_or_anti
#print axioms tent_width_tradeoff
#print axioms tent_widths_iff
#print axioms tent_first_one_iff
#print axioms tent_first_two_iff
#print axioms no_tent_zero_first
#print axioms no_tent_zero_second

end MaxCaterpillar.Frontier.WidthTradeoffAudit
