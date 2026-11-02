import MaxCaterpillar.Fiber.Count65.Star.FeatureSpace
import MaxCaterpillar.Fiber.Count65.HeadTopology
import MaxCaterpillar.Fiber.Count65.Topology

/-! # Actual star two-head reconstruction spaces

The intercept coefficients carry their ordinary Euclidean product topology.
The explicit readout homeomorphism transports them to the complete invariant
function space; the fixed-remainder fiber has exactly two connected components.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star

abbrev HeadCoefficientData := (Fin 4 → ℝ) × (Fin 4 → ℝ) × (Fin 4 → ℝ)

noncomputable def headDataHomeomorph {r : ℝ} (hr : 0<r) :
    HeadCoefficientData ≃ₜ HeadTopology.Data (featureSpace r) :=
  (Homeomorph.refl _).prodCongr
    ((coefficientReadoutHomeomorph hr).prodCongr (coefficientReadoutHomeomorph hr))

abbrev HeadCoefficientFiber {r : ℝ} (hr : 0<r) (L : featureSpace r) :=
  {p : HeadCoefficientData //
    (HeadTopology.toHeads ((headDataHomeomorph hr) p)).Reconstructs
      (L : InvariantState → ℝ)}

/-- Ordinary physical head coefficients and actual invariant-function heads
have homeomorphic exact reconstruction fibers. -/
noncomputable def headFiberHomeomorph {r : ℝ} (hr : 0<r) (L : featureSpace r) :
    HeadCoefficientFiber hr L ≃ₜ HeadTopology.Fiber (featureSpace r) L where
  toFun p := ⟨headDataHomeomorph hr p.val,p.property⟩
  invFun p := ⟨(headDataHomeomorph hr).symm p.val,by
    simpa only [Homeomorph.apply_symm_apply] using p.property⟩
  left_inv p := Subtype.ext ((headDataHomeomorph hr).symm_apply_apply p.val)
  right_inv p := Subtype.ext ((headDataHomeomorph hr).apply_symm_apply p.val)
  continuous_toFun := ((headDataHomeomorph hr).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((headDataHomeomorph hr).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

/-- The complete fixed nonzero actual remainder has precisely two head
reconstruction components. There is no restriction on incoming coefficients. -/
theorem has_two_head_components {r : ℝ} (hr : 0<r) (L : featureSpace r)
    (hL : ∃ x, (L : InvariantState → ℝ) x ≠ 0) :
    Nonempty (ConnectedComponents (HeadTopology.Fiber (featureSpace r) L) ≃ Fin 2) := by
  obtain ⟨A,B,hA,hB,hAB⟩ := exists_nonnegative_decomposition L.property
  have he : A-B=L := Subtype.ext hAB
  exact HeadTopology.has_two_head_components (featureSpace r)
    (clippingRigid_featureSpace hr) L A B hA hB he hL

/-- The same exact count in ordinary real head coefficients. -/
theorem coefficient_heads_have_two_components {r : ℝ} (hr : 0<r)
    (L : featureSpace r) (hL : ∃ x, (L : InvariantState → ℝ) x ≠ 0) :
    Nonempty (ConnectedComponents (HeadCoefficientFiber hr L) ≃ Fin 2) := by
  obtain ⟨e⟩ := has_two_head_components hr L hL
  exact ⟨(connectedComponentsEquivOfHomeomorph (headFiberHomeomorph hr L)).trans e⟩
end MaxCaterpillar.Fiber.Count65.Star
