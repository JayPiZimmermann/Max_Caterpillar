import MaxCaterpillar.Fiber.GatingAbstractions.Regularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Smooth ambient regularity, rather than merely a topological chart -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.GatingAbstractions
open Filter Topology

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- An ambient chart with invertible derivative, smooth forward and inverse
germs, and the whole fiber straightened to a coordinate plane. -/
def HasSmoothRegularFiberChartAt (S : Set E) (a : E) : Prop :=
  ∃ (e : PartialHomeomorph E (V × W)) (L : E ≃L[ℝ] (V × W)),
    a ∈ e.source ∧
    HasStrictFDerivAt (e : E → V × W) (L : E →L[ℝ] V × W) a ∧
    ContDiffAt ℝ ⊤ (e : E → V × W) a ∧
    ContDiffAt ℝ ⊤ (e.symm : V × W → E) (e a) ∧
    ∀ x ∈ e.source, x ∈ S ↔ (e x).1 = (e a).1

theorem HasSmoothRegularFiberChartAt.regular {S : Set E} {a : E}
    (h : HasSmoothRegularFiberChartAt (V := V) (W := W) S a) :
    HasRegularFiberChartAt (V := V) (W := W) S a := by
  rcases h with ⟨e,L,ha,hd,_,_,hplane⟩
  exact ⟨e,L,ha,hd,hplane⟩

/-- A smooth version of the exact-coordinate reconstruction criterion. -/
theorem smooth_regular_fiber_chart_of_inverse_coordinates
    (S : Set E) (F : E → V) (g : E → W) (P : W → E) (a : E)
    (L : E ≃L[ℝ] (V × W))
    (hL : HasStrictFDerivAt (fun x => (F x, g x))
      (L : E →L[ℝ] V × W) a)
    (hsm : ContDiffAt ℝ ⊤ (fun x => (F x, g x)) a)
    (hPg : P (g a) = a) (hPc : ContinuousAt P (g a))
    (hgc : ContinuousAt g a) (hobs : ∀ x ∈ S, F x = F a)
    (hPS : ∀ᶠ w in 𝓝 (g a), P w ∈ S)
    (hgP : ∀ᶠ w in 𝓝 (g a), g (P w) = w) :
    HasSmoothRegularFiberChartAt (V := V) (W := W) S a := by
  let H : E → V × W := fun x => (F x, g x)
  let e := hL.toPartialHomeomorph H
  have hmem : a ∈ e.source := hL.mem_toPartialHomeomorph_source
  have hlocal := eventual_fiber_iff_of_inverse_coordinates S F g P a L hL
    hPg hPc hgc hobs hPS hgP
  rcases mem_nhds_iff.mp hlocal with ⟨U, hU, hUopen, haU⟩
  let er := e.restrOpen U hUopen
  have har : a ∈ er.source := ⟨hmem,haU⟩
  have hdr : HasStrictFDerivAt (er : E → V × W) (L : E →L[ℝ] V × W) a := hL
  have hsr : ContDiffAt ℝ ⊤ (er : E → V × W) a := hsm
  refine ⟨er,L,har,hdr,hsr,?_,?_⟩
  · apply er.contDiffAt_symm (er.map_source har)
    · simpa only [er.left_inv har] using hdr.hasFDerivAt
    · simpa only [er.left_inv har] using hsr
  · intro x hx
    exact hU hx.2

#print axioms smooth_regular_fiber_chart_of_inverse_coordinates
end MaxCaterpillar.Fiber.GatingAbstractions
