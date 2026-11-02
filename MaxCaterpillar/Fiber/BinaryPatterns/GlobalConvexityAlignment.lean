import MaxCaterpillar.Fiber.BinaryPatterns.AffineHalfspace
import MaxCaterpillar.Fiber.BinaryPatterns.GlobalConvexityBias

/-! # Aligning globally equal first-layer binary gates -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.BinaryPatterns
open BigOperators Frontier unitInterval
variable {N h₁ h₂ : ℕ}

lemma firstPreactivation_scaleFirst (a : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (x : Point N) (j : Fin h₁) :
    (scaleFirst a s).firstPreactivation x j = s j*a.firstPreactivation x j := by
  unfold Network.firstPreactivation
  change (∑ i,s j*a.W₁ j i*x i)+s j*a.b₁ j = _
  rw [mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma firstHidden_scaleFirst (a : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (hs : ∀ j,0 < s j) (x : Point N) (j : Fin h₁) :
    (scaleFirst a s).firstHidden x j = s j*a.firstHidden x j := by
  change relu ((scaleFirst a s).firstPreactivation x j) = s j*relu (a.firstPreactivation x j)
  rw [firstPreactivation_scaleFirst,Frontier.relu_mul_pos (hs j)]

lemma firstBinary_scaleFirst (a : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (hs : ∀ j,0 < s j) (x : Point N) :
    (scaleFirst a s).firstBinary x = a.firstBinary x := by
  funext j
  have hiff : (scaleFirst a s).firstBinary x j = true ↔ a.firstBinary x j = true := by
    rw [Network.firstBinary_eq_true_iff,Network.firstBinary_eq_true_iff]
    change 0 < (scaleFirst a s).firstPreactivation x j ↔ 0 < a.firstPreactivation x j
    rw [firstPreactivation_scaleFirst]
    constructor
    · intro h
      by_contra hn
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (hs j).le (le_of_not_gt hn))) h
    · exact mul_pos (hs j)
  cases h1 : (scaleFirst a s).firstBinary x j <;>
    cases h2 : a.firstBinary x j <;> simp_all

lemma secondPreactivation_scaleFirst (a : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (hs : ∀ j,0 < s j) (x : Point N) (k : Fin h₂) :
    (scaleFirst a s).secondPreactivation x k = a.secondPreactivation x k := by
  unfold Network.secondPreactivation
  simp only [firstHidden_scaleFirst a s hs]
  change (∑ j,(a.W₂ k j/s j)*(s j*a.firstHidden x j))+a.b₂ k = _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  field_simp [ne_of_gt (hs j)]
  ring

lemma secondBinary_scaleFirst (a : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (hs : ∀ j,0 < s j) (x : Point N) :
    (scaleFirst a s).secondBinary x = a.secondBinary x := by
  funext k
  have hiff : (scaleFirst a s).secondBinary x k = true ↔ a.secondBinary x k = true := by
    rw [Network.secondBinary_eq_true_iff,Network.secondBinary_eq_true_iff]
    change 0 < (scaleFirst a s).secondPreactivation x k ↔ 0 < a.secondPreactivation x k
    rw [secondPreactivation_scaleFirst a s hs]
  cases h1 : (scaleFirst a s).secondBinary x k <;>
    cases h2 : a.secondBinary x k <;> simp_all

/-- Shared global first-layer binary maps allow positive first-neuron rescaling
that aligns the entire first matrix; any remaining bias discrepancy is inactive. -/
theorem exists_first_alignment (a b : Network N h₁ h₂)
    (hg : ∀ x,a.firstBinary x = b.firstBinary x) :
    ∃ s : Fin h₁ → ℝ, (∀ j,0 < s j) ∧
      (scaleFirst a s).W₁ = b.W₁ ∧ BiasCompatible (scaleFirst a s) b := by
  classical
  have per (j : Fin h₁) : ∃ s : ℝ,0 < s ∧ b.W₁ j = (fun i => s*a.W₁ j i) ∧
      (b.b₁ j = s*a.b₁ j ∨ (a.W₁ j = 0 ∧ a.b₁ j ≤ 0 ∧ b.b₁ j ≤ 0)) := by
    have hgate : ∀ x,0 < AffineHalfspace.affineValue (a.W₁ j) (a.b₁ j) x ↔
        0 < AffineHalfspace.affineValue (b.W₁ j) (b.b₁ j) x := by
      intro x
      change (0 < (∑ i,a.W₁ j i*x i)+a.b₁ j) ↔ (0 < (∑ i,b.W₁ j i*x i)+b.b₁ j)
      rw [←Network.firstBinary_eq_true_iff,←Network.firstBinary_eq_true_iff,hg x]
    rcases AffineHalfspace.binary_gate_alternatives (a.W₁ j) (b.W₁ j) (a.b₁ j) (b.b₁ j) hgate with
      hp | ⟨haw,hab,hbw,hbb⟩
    · obtain ⟨s,hs,hw,hb⟩ := hp
      exact ⟨s,hs,hw,Or.inl hb⟩
    · refine ⟨1,zero_lt_one,?_,Or.inr ⟨haw,hab,hbb⟩⟩
      rw [haw,hbw]
      funext _i
      simp
  choose s hs hw hb using per
  refine ⟨s,hs,?_,?_⟩
  · funext j
    exact (hw j).symm
  · intro j
    rcases hb j with hb | ⟨haw,hab,hbb⟩
    · exact Or.inl hb.symm
    · apply Or.inr
      refine ⟨?_,mul_nonpos_of_nonneg_of_nonpos (hs j).le hab,hbb⟩
      change (fun i => s j*a.W₁ j i) = 0
      rw [haw]
      funext _i
      simp

end MaxCaterpillar.Fiber.BinaryPatterns
