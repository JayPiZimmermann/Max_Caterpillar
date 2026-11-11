import Mathlib.Analysis.Calculus.Implicit

/-!
# Regular local charts from finite observations and exact coordinate families

These are generic inverse-function arguments. In the exact-fiber application,
finite observations supply one half of the local coordinates and an explicit
family of exact networks supplies the other half. The equality of the full
fiber with the regular level set is proved, not assumed in a new definition.
-/

set_option autoImplicit false

noncomputable section

namespace MaxCaterpillar.Fiber.GatingAbstractions

open Filter Topology

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A regular coordinate chart straightens a set to a coordinate plane.
The chart itself has an invertible strict derivative at the stated point.
Thus this is an ambient chart, not a parameterization of a curve or slice. -/
def HasRegularFiberChartAt (S : Set E) (a : E) : Prop :=
  ∃ (e : PartialHomeomorph E (V × W)) (L : E ≃L[ℝ] (V × W)),
    a ∈ e.source ∧
    HasStrictFDerivAt (e : E → V × W) (L : E →L[ℝ] V × W) a ∧
    ∀ x ∈ e.source, x ∈ S ↔ (e x).1 = (e a).1

/-- The inverse of a regular chart is strictly differentiable with the inverse
linear derivative. The chart is therefore differential, not just topological. -/
theorem HasRegularFiberChartAt.exists_chart_with_inverse_derivative
    {S : Set E} {a : E}
    (h : HasRegularFiberChartAt (V := V) (W := W) S a) :
    ∃ (e : PartialHomeomorph E (V × W)) (L : E ≃L[ℝ] (V × W)),
      a ∈ e.source ∧
      HasStrictFDerivAt (e : E → V × W) (L : E →L[ℝ] V × W) a ∧
      HasStrictFDerivAt (e.symm : V × W → E) (L.symm : V × W →L[ℝ] E) (e a) ∧
      ∀ x ∈ e.source, x ∈ S ↔ (e x).1 = (e a).1 := by
  rcases h with ⟨e, L, ha, hd, hplane⟩
  refine ⟨e, L, ha, hd, ?_, hplane⟩
  apply e.hasStrictFDerivAt_symm (e.map_source ha)
  simpa only [e.left_inv ha] using hd

/-- Finite observations determine the whole exact fiber locally if an explicit
continuous exact family realizes every nearby free coordinate and the combined
observation/free-coordinate map is locally invertible. -/
theorem eventual_fiber_iff_of_inverse_coordinates
    (S : Set E) (F : E → V) (g : E → W) (P : W → E) (a : E)
    (L : E ≃L[ℝ] (V × W))
    (hL : HasStrictFDerivAt (fun x => (F x, g x))
      (L : E →L[ℝ] V × W) a)
    (hPg : P (g a) = a)
    (hPc : ContinuousAt P (g a))
    (hgc : ContinuousAt g a)
    (hobs : ∀ x ∈ S, F x = F a)
    (hPS : ∀ᶠ w in 𝓝 (g a), P w ∈ S)
    (hgP : ∀ᶠ w in 𝓝 (g a), g (P w) = w) :
    ∀ᶠ x in 𝓝 a, x ∈ S ↔ F x = F a := by
  let H : E → V × W := fun x => (F x, g x)
  let invH : V × W → E := hL.localInverse H L a
  have hinv : ∀ᶠ x in 𝓝 a, invH (H x) = x := hL.eventually_left_inverse
  have hPg_cont : Tendsto (fun x => P (g x)) (𝓝 a) (𝓝 a) := by
    simpa only [hPg] using hPc.tendsto.comp hgc.tendsto
  have hnear := hPg_cont.eventually hinv
  have hPgood := hgc.tendsto.eventually hPS
  have hright := hgc.tendsto.eventually hgP
  filter_upwards [hinv, hnear, hPgood, hright] with x hx hPx hS hgp
  constructor
  · exact hobs x
  · intro hFx
    have hH : H (P (g x)) = H x := by
      apply Prod.ext
      · exact (hobs _ hS).trans hFx.symm
      · exact hgp
    have hEq : P (g x) = x := by
      rw [← hPx, hH, hx]
    exact hEq ▸ hS

/-- The full exact fiber has a regular ambient chart under the explicit
finite-observation and reconstruction hypotheses. -/
theorem regular_fiber_chart_of_inverse_coordinates
    (S : Set E) (F : E → V) (g : E → W) (P : W → E) (a : E)
    (L : E ≃L[ℝ] (V × W))
    (hL : HasStrictFDerivAt (fun x => (F x, g x))
      (L : E →L[ℝ] V × W) a)
    (hPg : P (g a) = a)
    (hPc : ContinuousAt P (g a))
    (hgc : ContinuousAt g a)
    (hobs : ∀ x ∈ S, F x = F a)
    (hPS : ∀ᶠ w in 𝓝 (g a), P w ∈ S)
    (hgP : ∀ᶠ w in 𝓝 (g a), g (P w) = w) :
    HasRegularFiberChartAt (V := V) (W := W) S a := by
  let H : E → V × W := fun x => (F x, g x)
  let e := hL.toPartialHomeomorph H
  have hmem : a ∈ e.source := hL.mem_toPartialHomeomorph_source
  have hlocal := eventual_fiber_iff_of_inverse_coordinates S F g P a L hL
    hPg hPc hgc hobs hPS hgP
  rcases mem_nhds_iff.mp hlocal with ⟨U, hU, hUopen, haU⟩
  refine ⟨e.restrOpen U hUopen, L, ⟨hmem, haU⟩, ?_, ?_⟩
  · exact hL
  · intro x hx
    exact hU hx.2

/-- A surjective strict derivative supplies a regular chart for its full level
set. This is the empirical-fiber application of the implicit function theorem. -/
theorem regular_level_set_chart [FiniteDimensional ℝ V]
    (F : E → V) (a : E) (F' : E →L[ℝ] V)
    (hF : HasStrictFDerivAt F F' a) (hF' : LinearMap.range F' = ⊤) :
    HasRegularFiberChartAt (V := V) (W := LinearMap.ker F')
      {x | F x = F a} a := by
  haveI : CompleteSpace V := FiniteDimensional.complete ℝ V
  let d := hF.implicitFunctionDataOfComplemented F F' hF'
    F'.ker_closedComplemented_of_finiteDimensional_range
  refine ⟨d.toPartialHomeomorph,
    d.leftDeriv.equivProdOfSurjectiveOfIsCompl d.rightDeriv
      d.left_range d.right_range d.isCompl_ker,
    d.pt_mem_toPartialHomeomorph_source, d.hasStrictFDerivAt, ?_⟩
  intro x hx
  rfl

#print axioms HasRegularFiberChartAt.exists_chart_with_inverse_derivative
#print axioms eventual_fiber_iff_of_inverse_coordinates
#print axioms regular_fiber_chart_of_inverse_coordinates
#print axioms regular_level_set_chart

end MaxCaterpillar.Fiber.GatingAbstractions
