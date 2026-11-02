import MaxCaterpillar.Fiber.BinaryPatterns.Core

set_option autoImplicit false
namespace MaxCaterpillar.Network
open BigOperators
variable {N h₁ h₂ : ℕ}

/-- Change only the second-layer matrix, preserving every other physical parameter. -/
def replaceSecondMatrix (a : Network N h₁ h₂) (W : Fin h₂ → Fin h₁ → ℝ) :
    Network N h₁ h₂ := ⟨a.W₁,a.b₁,W,a.b₂,a.w₃,a.b₃⟩

lemma replaceSecondMatrix_self (a : Network N h₁ h₂) :
    replaceSecondMatrix a a.W₂ = a := by cases a; rfl

lemma firstHidden_replaceSecondMatrix (a : Network N h₁ h₂)
    (W : Fin h₂ → Fin h₁ → ℝ) (x : Point N) :
    (replaceSecondMatrix a W).firstHidden x = a.firstHidden x := rfl

lemma secondHidden_replaceSecondMatrix (a : Network N h₁ h₂)
    (W : Fin h₂ → Fin h₁ → ℝ) (x : Point N) :
    (replaceSecondMatrix a W).secondHidden x =
      fun k => relu ((∑ j,W k j*a.firstHidden x j)+a.b₂ k) := rfl

lemma zeroBiases_replaceSecondMatrix (a : Network N h₁ h₂)
    (W : Fin h₂ → Fin h₁ → ℝ) :
    (replaceSecondMatrix a W).HasZeroBiases ↔ a.HasZeroBiases := Iff.rfl

lemma w₃_replaceSecondMatrix (a : Network N h₁ h₂)
    (W : Fin h₂ → Fin h₁ → ℝ) : (replaceSecondMatrix a W).w₃ = a.w₃ := rfl

lemma firstActiveCount_replaceSecondMatrix (a : Network N h₁ h₂)
    (W : Fin h₂ → Fin h₁ → ℝ) (x : Point N) :
    (replaceSecondMatrix a W).firstActiveCount x = a.firstActiveCount x := rfl

lemma secondActiveCount_of_secondHidden {a b : Network N h₁ h₂} (x : Point N)
    (h : a.secondHidden x = b.secondHidden x) :
    a.secondActiveCount x = b.secondActiveCount x := by
  unfold secondActiveCount secondBinary
  rw [h]

lemma eval_replaceSecondMatrix_of_secondHidden (a : Network N h₁ h₂)
    (W : Fin h₂ → Fin h₁ → ℝ) (x : Point N)
    (h : (replaceSecondMatrix a W).secondHidden x = a.secondHidden x) :
    (replaceSecondMatrix a W).eval x = a.eval x := by
  rw [eval_eq_secondHidden,eval_eq_secondHidden,h]
  rfl

theorem continuous_replaceSecondMatrix (a : Network N h₁ h₂) :
    Continuous (replaceSecondMatrix a) := by
  apply (Fiber.continuous_network_iff _).mpr
  exact ⟨continuous_const,continuous_const,continuous_id,
    continuous_const,continuous_const,continuous_const⟩

end MaxCaterpillar.Network

namespace MaxCaterpillar.Fiber.BinaryPatterns
example (s : ℝ) (x : Point 4) :
    (Network.replaceSecondMatrix (net 0)
      ![![0,1,0,0,1,0],![0,0,0,0,-s,1],![1,-1,1,-1,0,0]]).firstHidden x =
      (net 0).firstHidden x := Network.firstHidden_replaceSecondMatrix _ _ _
end MaxCaterpillar.Fiber.BinaryPatterns
