import MaxCaterpillar.Fiber.Count65.Star.ActualChartClass
import MaxCaterpillar.Fiber.Count65.Star.ActualChartClass.Connected
import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.QuotientCoverage
import MaxCaterpillar.Fiber.Count65.SectorQuotient.Labels

/-! # Complete star quotient label fibers are connected actual chart images

Coverage uses only genuine positive neuron rescalings and hidden permutations.
The labels are the previously proved continuous invariants of the full actual
symmetry quotient; equal network functions add no new identifications.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.ActualStarLabels
open Set Function Star Star65 Star.PhysicalChart SectorQuotient

noncomputable def physicalZeroBias (p : Slice) (hz : p.val.2.HasZeroBiases) :
    ZeroBiasFiber 4 6 5 := ⟨canonicalStarFiber p,hz⟩
noncomputable def chartIZeroBias (bits : Fin 3 → Bool) (q : ChartI bits) :
    ZeroBiasFiber 4 6 5 := physicalZeroBias (chartI bits q) (chartI_zeroBiases bits q)
noncomputable def chartIIZeroBias (bits : Fin 3 → Bool) (q : ChartII bits) :
    ZeroBiasFiber 4 6 5 := physicalZeroBias (chartII bits q) (chartII_zeroBiases bits q)

lemma continuous_chartIZeroBias (bits : Fin 3 → Bool) : Continuous (chartIZeroBias bits) :=
  ((continuous_branchIChart (chartFlipBits bits)).subtype_mk _).subtype_mk _
lemma continuous_chartIIZeroBias (bits : Fin 3 → Bool) : Continuous (chartIIZeroBias bits) :=
  ((continuous_branchIIChart (chartFlipBits bits)).subtype_mk _).subtype_mk _

noncomputable def chartIQuotient (bits : Fin 3 → Bool) (q : ChartI bits) :
    ZeroBiasSymmetryQuotient 4 6 5 := Quotient.mk _ (chartIZeroBias bits q)
noncomputable def chartIIQuotient (bits : Fin 3 → Bool) (q : ChartII bits) :
    ZeroBiasSymmetryQuotient 4 6 5 := Quotient.mk _ (chartIIZeroBias bits q)
lemma continuous_chartIQuotient (bits : Fin 3 → Bool) : Continuous (chartIQuotient bits) :=
  continuous_quotient_mk'.comp (continuous_chartIZeroBias bits)
lemma continuous_chartIIQuotient (bits : Fin 3 → Bool) : Continuous (chartIIQuotient bits) :=
  continuous_quotient_mk'.comp (continuous_chartIIZeroBias bits)

/-- The actual coefficient coverage descends to the genuine zero-bias
symmetry relation, with the chart/physical orientation conversion explicit. -/
theorem zeroBias_chart_quotient_covered (p : Slice) (hz : p.val.2.HasZeroBiases) :
    (∃ bits : Fin 3 → Bool,∃ q : ChartI bits,
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz)=chartIQuotient bits q) ∨
    (∃ bits : Fin 3 → Bool,∃ q : ChartII bits,
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz)=chartIIQuotient bits q) := by
  have hc := Star.PhysicalChart.zeroBias_quotient_covered (canonicalStarFiber p) (time p)
    p.property.1 p.property.2.1 hz p.property.2.2.1
  rcases hc with ⟨o,q,hq⟩ | ⟨o,q,hq⟩
  · obtain ⟨bits,hbits⟩ : ∃ bits : Fin 3 → Bool,chartFlipBits o=bits := ⟨_,rfl⟩
    have ho : o=chartFlipBits bits :=
      (chartFlipBits_involutive o).symm.trans (congrArg chartFlipBits hbits)
    subst o
    refine Or.inl ⟨bits,q,Quotient.sound ?_⟩
    change (symmetrySetoid 4 6 5).r (canonicalStarFiber p)
      (branchIExact (chartFlipBits bits) q)
    exact Quotient.exact hq
  · obtain ⟨bits,hbits⟩ : ∃ bits : Fin 3 → Bool,chartFlipBits o=bits := ⟨_,rfl⟩
    have ho : o=chartFlipBits bits :=
      (chartFlipBits_involutive o).symm.trans (congrArg chartFlipBits hbits)
    subst o
    refine Or.inr ⟨bits,q,Quotient.sound ?_⟩
    change (symmetrySetoid 4 6 5).r (canonicalStarFiber p)
      (branchIIExact (chartFlipBits bits) q)
    exact Quotient.exact hq

lemma starZeroBiasLabel_chartI (bits : Fin 3 → Bool) (kind : Bool)
    (q : ChartI bits) (hq : q ∈ headSectorI bits kind) :
    starZeroBiasLabel (chartIQuotient bits q)=some (false,bits,kind) := by
  have h := starZeroBiasLabel_canonical (chartI bits q) (chartI_zeroBiases bits q)
  change starZeroBiasLabel (chartIQuotient bits q)=some (componentLabel (chartI bits q)) at h
  simpa only [componentLabel_chartI bits kind q hq] using h
lemma starZeroBiasLabel_chartII (bits : Fin 3 → Bool) (kind : Bool)
    (q : ChartII bits) (hq : q ∈ headSectorII bits kind) :
    starZeroBiasLabel (chartIIQuotient bits q)=some (true,bits,kind) := by
  have h := starZeroBiasLabel_canonical (chartII bits q) (chartII_zeroBiases bits q)
  change starZeroBiasLabel (chartIIQuotient bits q)=some (componentLabel (chartII bits q)) at h
  simpa only [componentLabel_chartII bits kind q hq] using h

noncomputable def componentImage (l : NonpairedLabel) : Set (ZeroBiasSymmetryQuotient 4 6 5) :=
  if l.1 then chartIIQuotient l.2.1 '' headSectorII l.2.1 l.2.2
  else chartIQuotient l.2.1 '' headSectorI l.2.1 l.2.2

theorem isPathConnected_componentImage (l : NonpairedLabel) : IsPathConnected (componentImage l) := by
  rcases l with ⟨b,bits,kind⟩
  cases b
  · exact (isPathConnected_headSectorI bits kind).image (continuous_chartIQuotient bits)
  · exact (isPathConnected_headSectorII bits kind).image (continuous_chartIIQuotient bits)

/-- The entire some-label fiber of the full actual symmetry quotient equals
one matching connected physical chart/head-kind image. -/
theorem starLabel_fiber (l : NonpairedLabel) :
    starZeroBiasLabel ⁻¹' {some l}=componentImage l := by
  ext z
  constructor
  · intro hz
    obtain ⟨p,hp,hPz,_⟩ := starZeroBiasLabel_some_covered z l hz
    change Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hp)=z at hPz
    rcases zeroBias_chart_quotient_covered p hp with ⟨bits,q,hQ⟩ | ⟨bits,q,hQ⟩
    · obtain ⟨kind,hq⟩ := headSectorI_exhaustive bits q
      have hQz : chartIQuotient bits q=z := hQ.symm.trans hPz
      have hl : (false,bits,kind)=l := by
        apply Option.some.inj
        calc
          some (false,bits,kind)=starZeroBiasLabel (chartIQuotient bits q) :=
            (starZeroBiasLabel_chartI bits kind q hq).symm
          _ = starZeroBiasLabel z := congrArg starZeroBiasLabel hQz
          _ = some l := hz
      rw [← hl]
      change z ∈ chartIQuotient bits '' headSectorI bits kind
      exact ⟨q,hq,hQz⟩
    · obtain ⟨kind,hq⟩ := headSectorII_exhaustive bits q
      have hQz : chartIIQuotient bits q=z := hQ.symm.trans hPz
      have hl : (true,bits,kind)=l := by
        apply Option.some.inj
        calc
          some (true,bits,kind)=starZeroBiasLabel (chartIIQuotient bits q) :=
            (starZeroBiasLabel_chartII bits kind q hq).symm
          _ = starZeroBiasLabel z := congrArg starZeroBiasLabel hQz
          _ = some l := hz
      rw [← hl]
      change z ∈ chartIIQuotient bits '' headSectorII bits kind
      exact ⟨q,hq,hQz⟩
  · intro hz
    rcases l with ⟨b,bits,kind⟩
    cases b
    · obtain ⟨q,hq,rfl⟩ := hz
      exact starZeroBiasLabel_chartI bits kind q hq
    · obtain ⟨q,hq,rfl⟩ := hz
      exact starZeroBiasLabel_chartII bits kind q hq

/-- Every concrete star label fiber is path connected in the genuine full
zero-bias symmetry quotient, with every actual endpoint and symmetry restored. -/
theorem isPathConnected_starLabel_fiber (l : NonpairedLabel) :
    IsPathConnected (starZeroBiasLabel ⁻¹' {some l}) := by
  rw [starLabel_fiber]
  exact isPathConnected_componentImage l

#print axioms zeroBias_chart_quotient_covered
#print axioms starLabel_fiber
#print axioms isPathConnected_starLabel_fiber
end MaxCaterpillar.Fiber.Count65.ActualStarLabels
