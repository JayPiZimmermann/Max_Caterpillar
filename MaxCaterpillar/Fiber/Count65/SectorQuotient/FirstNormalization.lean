import MaxCaterpillar.Fiber.Symmetry

/-! Continuous first-neuron normalization in all physical network arrays. -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

variable {N h₁ h₂ : ℕ}

lemma continuous_variable_scaleFirst {X : Type*} [TopologicalSpace X]
    (f : X → Network N h₁ h₂) (s : X → Fin h₁ → ℝ)
    (hf : Continuous f) (hs : Continuous s) (hz : ∀ x j, s x j ≠ 0) :
    Continuous (fun x => scaleFirst (f x) (s x)) := by
  apply (continuous_network_iff _).mpr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · apply continuous_pi
    intro j
    apply continuous_pi
    intro i
    exact ((continuous_apply j).comp hs).mul
      ((continuous_apply i).comp ((continuous_apply j).comp (continuous_W₁.comp hf)))
  · apply continuous_pi
    intro j
    exact ((continuous_apply j).comp hs).mul
      ((continuous_apply j).comp (continuous_b₁.comp hf))
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    exact ((continuous_apply j).comp ((continuous_apply k).comp (continuous_W₂.comp hf))).div
      ((continuous_apply j).comp hs) (fun x => hz x j)
  · change Continuous (fun x => (f x).b₂)
    exact continuous_b₂.comp hf
  · change Continuous (fun x => (f x).w₃)
    exact continuous_w₃.comp hf
  · change Continuous (fun x => (f x).b₃)
    exact continuous_b₃.comp hf

lemma reciprocal_first_weights (net : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (rows : Fin h₁ → Fin N → ℝ) (hs : ∀ j, s j ≠ 0)
    (hw : net.W₁ = fun j i => s j * rows j i) :
    (scaleFirst net (fun j => (s j)⁻¹)).W₁ = rows := by
  funext j i
  change (s j)⁻¹ * net.W₁ j i = rows j i
  rw [hw, ← mul_assoc, inv_mul_cancel (hs j), one_mul]

end MaxCaterpillar.Fiber.Count65.SectorQuotient
