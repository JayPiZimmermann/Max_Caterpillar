import MaxCaterpillar.Fiber.Count65.Mixed.GeometricComponents
import MaxCaterpillar.Fiber.Count65.Star.FullSectorComponents
import MaxCaterpillar.Fiber.Count65.AtLeast65
import MaxCaterpillar.Fiber.Count65.GlobalLabelFibers
import MaxCaterpillar.Fiber.Count65.Paired.Connected

/-! # Actual component fibers of the full Max4 physical symmetry quotient

The complete actual all-input Max4 fiber has exactly 65 components after
positive hidden rescalings and hidden/input permutations, including arbitrary
biases. The paired and nonpaired deformation proofs establish every fiber
of the explicit global label; no normal-form hypothesis is an input.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65
open Set SectorQuotient

lemma global_mixed_fiber_eq (l : NonpairedLabel) :
    globalLabel ⁻¹' {Sum.inr (Sum.inl l)}=mixedZeroBiasLabel ⁻¹' {some l} := by
  ext z
  exact globalLabel_mixed z l

theorem isPathConnected_global_mixed_fiber (l : NonpairedLabel) :
    IsPathConnected (globalLabel ⁻¹' {Sum.inr (Sum.inl l)}) := by
  rw [global_mixed_fiber_eq]
  exact MixedFullSectorComponents.isPathConnected_mixedLabel_fiber l

lemma global_star_fiber_eq (l : NonpairedLabel) :
    globalLabel ⁻¹' {Sum.inr (Sum.inr l)}=starZeroBiasLabel ⁻¹' {some l} := by
  ext z
  exact globalLabel_star z l

theorem isPathConnected_global_star_fiber (l : NonpairedLabel) :
    IsPathConnected (globalLabel ⁻¹' {Sum.inr (Sum.inr l)}) := by
  rw [global_star_fiber_eq]
  exact ActualStarLabels.isPathConnected_starLabel_fiber l

/-- Internal assembly only: the paired connectedness proof is supplied by
its separate actual deformation module. All 64 other fibers are already
proved connected above; no classification hypothesis remains here. -/
private noncomputable def componentsEquiv65_of_paired
    (hP : IsPathConnected Paired.quotientSector) :
    ConnectedComponents (ZeroBiasSymmetryQuotient 4 6 5) ≃ Fin 65 := by
  letI : TotallySeparatedSpace ComponentLabel := TotallySeparatedSpace.of_discrete ComponentLabel
  letI : TotallyDisconnectedSpace ComponentLabel :=
    TotallySeparatedSpace.totallyDisconnectedSpace ComponentLabel
  have hf : ∀ l : ComponentLabel,IsPreconnected (globalLabel ⁻¹' {l}) := by
    intro l
    rcases l with u | l
    · cases u
      rw [global_paired_fiber_eq]
      exact hP.isConnected.2
    · rcases l with m | s
      · exact (isPathConnected_global_mixed_fiber m).isConnected.2
      · exact (isPathConnected_global_star_fiber s).isConnected.2
  exact (connectedComponentsEquiv continuous_globalLabel globalLabel_surjective hf).trans
    componentLabelEquivFin65

/-- Exact classification of every zero-bias genuine quotient component. -/
noncomputable def zeroBiasComponentsEquiv65 :
    ConnectedComponents (ZeroBiasSymmetryQuotient 4 6 5) ≃ Fin 65 :=
  componentsEquiv65_of_paired Paired.isPathConnected_quotientSector

/-- Allowing arbitrary biases preserves the exact count by the verified
bias deformation on the genuine physical symmetry quotient. -/
noncomputable def fullComponentsEquiv65 :
    ConnectedComponents (SymmetryQuotient 4 6 5) ≃ Fin 65 :=
  zeroBiasQuotientConnectedComponentsEquiv.trans zeroBiasComponentsEquiv65

#print axioms isPathConnected_global_mixed_fiber
#print axioms isPathConnected_global_star_fiber
#print axioms global_paired_fiber_eq
#print axioms zeroBiasComponentsEquiv65
#print axioms fullComponentsEquiv65
end MaxCaterpillar.Fiber.Count65

namespace MaxCaterpillar.Fiber

/-- The full real Max4 (6,5) exact fiber, with arbitrary biases and precisely
positive hidden rescalings and hidden/input permutations quotiented, has
exactly 65 connected components. No classification assumptions are inputs. -/
theorem max4_6_5_has_65_components : HasComponentCount 4 6 5 65 :=
  ⟨Count65.fullComponentsEquiv65⟩

theorem max4_6_5_component_count_eq_65 :
    Nat.card (ConnectedComponents (SymmetryQuotient 4 6 5))=65 := by
  calc
    Nat.card (ConnectedComponents (SymmetryQuotient 4 6 5))=Nat.card (Fin 65) :=
      Nat.card_congr Count65.fullComponentsEquiv65
    _ = 65 := by simp

#print axioms max4_6_5_has_65_components
#print axioms max4_6_5_component_count_eq_65
end MaxCaterpillar.Fiber
