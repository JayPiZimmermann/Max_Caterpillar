import MaxCaterpillar.Fiber.Count65.AtLeast65.GlobalLabel
import MaxCaterpillar.Fiber.Count65.Paired.QuotientSector

/-! # Paths and geometric fibers of the actual global component label -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65
open Set SectorQuotient

/-- The Unit fiber is precisely the actual geometric paired quotient image. -/
theorem global_paired_fiber_eq :
    globalLabel ⁻¹' {Sum.inl ()}=Paired.quotientSector := by
  ext z
  induction z using Quotient.inductionOn with
  | h x =>
    constructor
    · intro hz
      have hx := (globalLabel_paired_mk x).mp hz
      exact ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      rw [← he]
      exact (globalLabel_paired_mk y).mpr hy

/-- Every actual quotient path starting in a global label fiber remains in
that fiber, since a continuous map from the interval to a discrete space is
constant. Completion paths therefore need no extra first-frame annotation. -/
theorem joinedIn_globalLabel_fiber {x y : ZeroBiasSymmetryQuotient 4 6 5}
    (h : Joined x y) (l : ComponentLabel) (hx : globalLabel x=l) :
    JoinedIn (globalLabel ⁻¹' {l}) x y := by
  obtain ⟨γ⟩ := h
  refine ⟨γ,?_⟩
  intro t
  change globalLabel (γ t)=l
  have hc : Continuous (fun t => globalLabel (γ t)) := continuous_globalLabel.comp γ.continuous
  have he : globalLabel (γ t)=globalLabel (γ 0) :=
    isPreconnected_univ.constant hc.continuousOn (Set.mem_univ t) (Set.mem_univ 0)
  exact he.trans ((congrArg globalLabel γ.source).trans hx)

theorem joinedIn_paired_quotientSector {x y : ZeroBiasSymmetryQuotient 4 6 5}
    (hx : x ∈ Paired.quotientSector) (h : Joined x y) :
    JoinedIn Paired.quotientSector x y := by
  have hl : globalLabel x=Sum.inl () := by
    change x ∈ globalLabel ⁻¹' {Sum.inl ()}
    rw [global_paired_fiber_eq]
    exact hx
  have hj := joinedIn_globalLabel_fiber h (Sum.inl ()) hl
  rw [global_paired_fiber_eq] at hj
  exact hj

#print axioms global_paired_fiber_eq
#print axioms joinedIn_paired_quotientSector
end MaxCaterpillar.Fiber.Count65
