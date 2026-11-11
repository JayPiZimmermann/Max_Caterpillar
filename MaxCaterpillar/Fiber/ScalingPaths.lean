import MaxCaterpillar.Fiber.Symmetry
import Mathlib.Topology.Connected.PathConnected

/-! # Positive scaling paths in the exact parameter fiber

Strictly positive scales interpolate to one without vanishing. Compensation
in the next affine map stays continuous throughout this interpolation, even
when the network itself has zero weights or unused neurons.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

open unitInterval

variable {N h₁ h₂ m : ℕ}

/-- The straight segment of scales from the identity to `s`. -/
def scaleSegment (s : Fin m → ℝ) (t : I) (j : Fin m) : ℝ :=
  1 - (t : ℝ) + (t : ℝ) * s j

theorem scaleSegment_pos (s : Fin m → ℝ) (hs : ∀ j, 0 < s j)
    (t : I) (j : Fin m) : 0 < scaleSegment s t j := by
  unfold scaleSegment
  by_cases ht : (t : ℝ) = 0
  · simp [ht]
  · have hp : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have hm : 0 < (t : ℝ) * s j := mul_pos hp (hs j)
    linarith [t.property.2]

theorem continuous_scaleSegment (s : Fin m → ℝ) (j : Fin m) :
    Continuous (fun t : I => scaleSegment s t j) :=
  (continuous_const.sub continuous_subtype_val).add (continuous_subtype_val.mul continuous_const)

theorem continuous_scaleFirst_segment (net : Network N h₁ h₂)
    (s : Fin h₁ → ℝ) (hs : ∀ j, 0 < s j) :
    Continuous (fun t : I => scaleFirst net (scaleSegment s t)) := by
  apply (continuous_network_iff _).2
  refine ⟨?_, ?_, ?_, continuous_const, continuous_const, continuous_const⟩
  · apply continuous_pi
    intro j
    apply continuous_pi
    intro i
    exact (continuous_scaleSegment s j).mul continuous_const
  · apply continuous_pi
    intro j
    exact (continuous_scaleSegment s j).mul continuous_const
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    exact continuous_const.div (continuous_scaleSegment s j)
      (fun t => ne_of_gt (scaleSegment_pos s hs t j))

theorem continuous_scaleSecond_segment (net : Network N h₁ h₂)
    (s : Fin h₂ → ℝ) (hs : ∀ k, 0 < s k) :
    Continuous (fun t : I => scaleSecond net (scaleSegment s t)) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, ?_, ?_, ?_, continuous_const⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    exact (continuous_scaleSegment s k).mul continuous_const
  · apply continuous_pi
    intro k
    exact (continuous_scaleSegment s k).mul continuous_const
  · apply continuous_pi
    intro k
    exact continuous_const.div (continuous_scaleSegment s k)
      (fun t => ne_of_gt (scaleSegment_pos s hs t k))

variable [NeZero N]

/-- A path of exact networks from a network to any positive first-layer rescaling. -/
noncomputable def scaleFirstPath (s : Fin h₁ → ℝ) (hs : ∀ j, 0 < s j)
    (net : ExactFiber N h₁ h₂) : Path net (scaleFirstFiber s hs net) where
  toFun t := scaleFirstFiber (scaleSegment s t) (scaleSegment_pos s hs t) net
  continuous_toFun := (continuous_scaleFirst_segment net.val s hs).subtype_mk _
  source' := by
    apply Subtype.ext
    simp [scaleFirstFiber, scaleFirst, scaleSegment]
  target' := by
    apply Subtype.ext
    simp [scaleFirstFiber, scaleFirst, scaleSegment]

/-- A path of exact networks from a network to any positive second-layer rescaling. -/
noncomputable def scaleSecondPath (s : Fin h₂ → ℝ) (hs : ∀ k, 0 < s k)
    (net : ExactFiber N h₁ h₂) : Path net (scaleSecondFiber s hs net) where
  toFun t := scaleSecondFiber (scaleSegment s t) (scaleSegment_pos s hs t) net
  continuous_toFun := (continuous_scaleSecond_segment net.val s hs).subtype_mk _
  source' := by
    apply Subtype.ext
    simp [scaleSecondFiber, scaleSecond, scaleSegment]
  target' := by
    apply Subtype.ext
    simp [scaleSecondFiber, scaleSecond, scaleSegment]

@[simp] theorem scaleFirstPath_apply (s : Fin h₁ → ℝ) (hs : ∀ j, 0 < s j)
    (net : ExactFiber N h₁ h₂) (t : I) :
    scaleFirstPath s hs net t =
      scaleFirstFiber (scaleSegment s t) (scaleSegment_pos s hs t) net := rfl

@[simp] theorem scaleSecondPath_apply (s : Fin h₂ → ℝ) (hs : ∀ k, 0 < s k)
    (net : ExactFiber N h₁ h₂) (t : I) :
    scaleSecondPath s hs net t =
      scaleSecondFiber (scaleSegment s t) (scaleSegment_pos s hs t) net := rfl

theorem joined_scaleFirst (s : Fin h₁ → ℝ) (hs : ∀ j, 0 < s j)
    (net : ExactFiber N h₁ h₂) : Joined net (scaleFirstFiber s hs net) :=
  ⟨scaleFirstPath s hs net⟩

theorem joined_scaleSecond (s : Fin h₂ → ℝ) (hs : ∀ k, 0 < s k)
    (net : ExactFiber N h₁ h₂) : Joined net (scaleSecondFiber s hs net) :=
  ⟨scaleSecondPath s hs net⟩

theorem scaleFirst_components_eq (s : Fin h₁ → ℝ) (hs : ∀ j, 0 < s j)
    (net : ExactFiber N h₁ h₂) :
    ConnectedComponents.mk net = ConnectedComponents.mk (scaleFirstFiber s hs net) :=
  ConnectedComponents.coe_eq_coe'.2
    (pathComponent_subset_component _ (joined_scaleFirst s hs net).symm)

theorem scaleSecond_components_eq (s : Fin h₂ → ℝ) (hs : ∀ k, 0 < s k)
    (net : ExactFiber N h₁ h₂) :
    ConnectedComponents.mk net = ConnectedComponents.mk (scaleSecondFiber s hs net) :=
  ConnectedComponents.coe_eq_coe'.2
    (pathComponent_subset_component _ (joined_scaleSecond s hs net).symm)

end MaxCaterpillar.Fiber
