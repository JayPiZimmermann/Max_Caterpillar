import research.sN.fiber_padding.strong.Strong
import MaxCaterpillar.Frontier.Main

/-! # Two always-active second-hidden-layer neurons with opposite output signs

The sign hypothesis in `SecondActiveSameSign` cannot be dropped: the exact Max2 network
`activeNet` of widths (3,2),

  `max(x₀,x₁) = σ(σ(x₀ - x₁) + σ(x₁)) - σ(σ(-x₁))`,

has two second-hidden-layer neurons that are active at every input (their preactivations
are sums of first-layer outputs), with output weights `1` and `-1`.  The architecture (3,2)
is minimal for `N = 2`, so no exact network of these widths has a removable neuron, and
therefore none has a mergeable or redundant neuron.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Padding.Strong

open BigOperators MaxCaterpillar.Fiber.Padding

theorem maximum_two (x : Point 2) : Maximum 2 x = max (x 0) (x 1) := by
  refine le_antisymm ((Frontier.Maximum_le_iff _ _).2 fun i => ?_)
    (max_le (Frontier.le_Maximum x 0) (Frontier.le_Maximum x 1))
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem max_key (a b : ℝ) : relu (relu (a - b) + relu b) - relu (relu (-b)) = max a b := by
  rw [relu_of_nonneg (add_nonneg (relu_nonneg' _) (relu_nonneg' _)),
    relu_of_nonneg (relu_nonneg' (-b))]
  rcases le_total a b with h | h <;> rcases le_total 0 b with hb | hb
  · rw [relu_of_nonpos (sub_nonpos.mpr h), relu_of_nonneg hb,
      relu_of_nonpos (neg_nonpos.mpr hb), max_eq_right h]
    ring
  · rw [relu_of_nonpos (sub_nonpos.mpr h), relu_of_nonpos hb,
      relu_of_nonneg (neg_nonneg.mpr hb), max_eq_right h]
    ring
  · rw [relu_of_nonneg (sub_nonneg.mpr h), relu_of_nonneg hb,
      relu_of_nonpos (neg_nonpos.mpr hb), max_eq_left h]
    ring
  · rw [relu_of_nonneg (sub_nonneg.mpr h), relu_of_nonpos hb,
      relu_of_nonneg (neg_nonneg.mpr hb), max_eq_left h]
    ring

/-- `max(x₀,x₁) = σ(σ(x₀ - x₁) + σ(x₁)) - σ(σ(-x₁))`. -/
noncomputable def activeNet : Network 2 3 2 where
  W₁ := ![![1, -1], ![0, 1], ![0, -1]]
  b₁ := 0
  W₂ := ![![1, 1, 0], ![0, 0, 1]]
  b₂ := 0
  w₃ := ![1, -1]
  b₃ := 0

theorem activeNet_act₁ (x : Point 2) :
    act₁ activeNet 0 x = relu (x 0 - x 1) ∧ act₁ activeNet 1 x = relu (x 1) ∧
      act₁ activeNet 2 x = relu (-x 1) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold act₁
    congr 1
    simp [activeNet, Fin.sum_univ_two]
    ring
  · unfold act₁
    congr 1
    simp [activeNet, Fin.sum_univ_two]
  · unfold act₁
    congr 1
    simp [activeNet, Fin.sum_univ_two]

theorem activeNet_pre₂ (x : Point 2) :
    pre₂ activeNet 0 x = relu (x 0 - x 1) + relu (x 1) ∧
      pre₂ activeNet 1 x = relu (-x 1) := by
  obtain ⟨h0, h1, h2⟩ := activeNet_act₁ x
  refine ⟨?_, ?_⟩
  · unfold pre₂
    rw [Fin.sum_univ_three, h0, h1, h2]
    simp [activeNet]
  · unfold pre₂
    rw [Fin.sum_univ_three, h0, h1, h2]
    simp [activeNet]

theorem activeNet_eval (x : Point 2) : activeNet.eval x = Maximum 2 x := by
  obtain ⟨h0, h1⟩ := activeNet_pre₂ x
  rw [maximum_two, ← max_key (x 0) (x 1), Strong.eval_eq, Fin.sum_univ_two]
  unfold act₂
  rw [h0, h1]
  simp [activeNet]
  ring

/-- No network with a single second-hidden-layer neuron computes `max₂`. -/
theorem no_exact_second_width_one {h₁ : ℕ} (net : Network 2 h₁ 1) :
    ¬ ∀ x, net.eval x = Maximum 2 x := by
  intro h
  have hval : ∀ t : ℝ, net.w₃ 0 * act₂ net 0 (fun _ => t) + net.b₃ = t := by
    intro t
    have := h (fun _ => t)
    rw [Strong.eval_eq, Fin.sum_univ_one, maximum_two, max_self] at this
    exact this
  rcases le_total 0 (net.w₃ 0) with hw | hw
  · have h1 := hval (net.b₃ - 1)
    have h2 := mul_nonneg hw (relu_nonneg' (pre₂ net 0 (fun _ => net.b₃ - 1)))
    unfold act₂ at h1
    linarith
  · have h1 := hval (net.b₃ + 1)
    have h2 := mul_nonpos_of_nonpos_of_nonneg hw (relu_nonneg' (pre₂ net 0 (fun _ => net.b₃ + 1)))
    unfold act₂ at h1
    linarith

/-- The widths (3,2) are minimal for `max₂`: no exact network has a removable neuron. -/
theorem max2_3_2_no_removable (net : Network 2 3 2) (hnet : ∀ x, net.eval x = Maximum 2 x) :
    ¬ HasRemovableNeuron net := by
  rintro (⟨j, hj⟩ | ⟨k, hk⟩)
  · have h := Frontier.first_width_ge_succ (removeFirst (h₁ := 2) net j)
      (fun x => (removeFirst_eval net j hj x).trans (hnet x))
    exact absurd h (by norm_num)
  · exact no_exact_second_width_one (removeSecond (h₂ := 1) net k)
      (fun x => (removeSecond_eval net k hk x).trans (hnet x))

theorem max2_3_2_no_mergeableOrRedundant (net : Network 2 3 2)
    (hnet : ∀ x, net.eval x = Maximum 2 x) : ¬ HasMergeableOrRedundantNeuron net := by
  intro h
  obtain ⟨net', -, hrem⟩ := exists_joined_hasRemovableNeuron ⟨net, hnet⟩ h
  exact max2_3_2_no_removable net'.val net'.property hrem

/-- **Counterexample.** An exact network with two distinct second-hidden-layer neurons, both
active at every input, with output weights of strictly opposite signs, which has no
mergeable or redundant neuron and whose component is not reducible. -/
theorem active_opposite_sign_not_reducible :
    ∃ net : ExactFiber 2 3 2,
      (∃ k k' : Fin 2, k ≠ k' ∧ (∀ x, 0 ≤ pre₂ net.val k x) ∧ (∀ x, 0 ≤ pre₂ net.val k' x) ∧
        net.val.w₃ k * net.val.w₃ k' < 0) ∧
      ¬ HasMergeableOrRedundantNeuron net.val ∧
      ¬ IsReducibleComponent ((quotientMk net : SymmetryQuotient 2 3 2) :
        ConnectedComponents (SymmetryQuotient 2 3 2)) := by
  refine ⟨⟨activeNet, activeNet_eval⟩, ⟨0, 1, by decide, fun x => ?_, fun x => ?_, ?_⟩,
    max2_3_2_no_mergeableOrRedundant _ activeNet_eval, ?_⟩
  · rw [(activeNet_pre₂ x).1]
    exact add_nonneg (relu_nonneg' _) (relu_nonneg' _)
  · rw [(activeNet_pre₂ x).2]
    exact relu_nonneg' _
  · simp [activeNet]
  · rintro ⟨net, hrem, -⟩
    exact max2_3_2_no_removable net.val net.property hrem

#print axioms active_opposite_sign_not_reducible
#print axioms max2_3_2_no_mergeableOrRedundant

end MaxCaterpillar.Fiber.Padding.Strong
