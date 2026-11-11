import MaxCaterpillar.Fiber.Count65.Mixed.ChartClassFibers
import MaxCaterpillar.Fiber.Count65.SectorQuotient.Labels

/-! # The 32 components of the actual mixed symmetry-quotient sector -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.MixedFullSectorComponents
open Set Mixed65 ActualMixedLabels MixedSectorComponents MixedQuotientCharts MixedClassFibers
open SectorQuotient

noncomputable def componentImage (l : NonpairedLabel) : Set (ZeroBiasSymmetryQuotient 4 6 5) :=
  if l.1 then chartBQuotient l.2.1 '' headSectorB l.2.1 l.2.2
  else chartAQuotient l.2.1 '' headSectorA l.2.1 l.2.2

lemma isPathConnected_componentImage (l : NonpairedLabel) : IsPathConnected (componentImage l) := by
  rcases l with ⟨b,bits,kind⟩
  cases b
  · exact isPathConnected_quotientChartA bits kind
  · exact isPathConnected_quotientChartB bits kind

/-- The full genuine quotient fiber equals the matching connected actual
chart image. Both coverage and absence of further label identifications have
been proved for physical network symmetries. -/
theorem mixedLabel_fiber (l : NonpairedLabel) :
    mixedZeroBiasLabel ⁻¹' {some l}=componentImage l := by
  rcases l with ⟨b,bits,kind⟩
  ext z
  constructor
  · intro hz
    obtain ⟨p,hp,hQ,hlabel⟩ := mixedZeroBiasLabel_some_covered z (b,bits,kind) hz
    change Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hp)=z at hQ
    let l := actualLabel p
    have hl : p ∈ physicalClass l := actualLabel_mem p
    have hb : branch l=b := congrArg Prod.fst hlabel
    have hi : orientations l=bits := congrArg (fun x : NonpairedLabel => x.2.1) hlabel
    have hk : signed l=kind := congrArg (fun x : NonpairedLabel => x.2.2) hlabel
    cases b
    · have hmem := classA_quotient_covered_kind p l hl hp hb
      rw [hi,hk] at hmem
      change z ∈ chartAQuotient bits '' headSectorA bits kind
      rwa [hQ] at hmem
    · have hmem := classB_quotient_covered_kind p l hl hp hb
      rw [hi,hk] at hmem
      change z ∈ chartBQuotient bits '' headSectorB bits kind
      rwa [hQ] at hmem
  · intro hz
    cases b
    · obtain ⟨q,hq,rfl⟩ := hz
      have h := mixedZeroBiasLabel_canonical (chartA bits q)
        (residualLift_hasZeroBiases _ _ _ _ _)
      change mixedZeroBiasLabel (chartAQuotient bits q)=some (false,bits,kind)
      simpa only [componentLabel_chartA bits kind q hq] using h
    · obtain ⟨q,hq,rfl⟩ := hz
      have h := mixedZeroBiasLabel_canonical (chartB bits q)
        (residualLift_hasZeroBiases _ _ _ _ _)
      change mixedZeroBiasLabel (chartBQuotient bits q)=some (true,bits,kind)
      simpa only [componentLabel_chartB bits kind q hq] using h

lemma isPathConnected_mixedLabel_fiber (l : NonpairedLabel) :
    IsPathConnected (mixedZeroBiasLabel ⁻¹' {some l}) := by
  rw [mixedLabel_fiber]
  exact isPathConnected_componentImage l

/-- Actual mixed points of the genuine zero-bias symmetry quotient. -/
abbrev MixedQuotientSector :=
  {z : ZeroBiasSymmetryQuotient 4 6 5 // ∃ l,mixedZeroBiasLabel z=some l}

def labelClass (l : NonpairedLabel) : Set MixedQuotientSector :=
  {z | mixedZeroBiasLabel z.val=some l}

lemma isClosed_labelClass (l : NonpairedLabel) : IsClosed (labelClass l) :=
  isClosed_eq (continuous_mixedZeroBiasLabel.comp continuous_subtype_val) continuous_const

lemma labelClass_cover (z : MixedQuotientSector) : ∃ l,z ∈ labelClass l := z.property
lemma labelClass_unique (z : MixedQuotientSector) (l m : NonpairedLabel)
    (hl : z ∈ labelClass l) (hm : z ∈ labelClass m) : l=m :=
  Option.some.inj (hl.symm.trans hm)

lemma isPathConnected_labelClass (l : NonpairedLabel) : IsPathConnected (labelClass l) := by
  have hi : Inducing (Subtype.val : MixedQuotientSector → ZeroBiasSymmetryQuotient 4 6 5) :=
    inducing_subtype_val
  apply hi.isPathConnected_iff.mpr
  have he : (Subtype.val : MixedQuotientSector → ZeroBiasSymmetryQuotient 4 6 5) '' labelClass l=
      mixedZeroBiasLabel ⁻¹' {some l} := by
    ext z
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact hp
    · intro hz
      exact ⟨⟨z,⟨l,hz⟩⟩,hz,rfl⟩
  rw [he]
  exact isPathConnected_mixedLabel_fiber l

noncomputable def mixedComponentsEquiv : ConnectedComponents MixedQuotientSector ≃ NonpairedLabel := by
  let label := FiniteClosedPartition.classify labelClass labelClass_cover
  have hc : Continuous label := FiniteClosedPartition.continuous_classify
    labelClass isClosed_labelClass labelClass_cover labelClass_unique
  have hs : Function.Surjective label := by
    intro l
    obtain ⟨z,hz,_⟩ := isPathConnected_labelClass l
    exact ⟨z,(FiniteClosedPartition.classify_eq_iff labelClass labelClass_cover labelClass_unique z l).mpr hz⟩
  have hf : ∀ l,IsPreconnected (label ⁻¹' {l}) := by
    intro l
    have he : label ⁻¹' {l}=labelClass l := by
      ext z
      exact FiniteClosedPartition.classify_eq_iff labelClass labelClass_cover labelClass_unique z l
    rw [he]
    exact (isPathConnected_labelClass l).isConnected.2
  exact connectedComponentsEquiv hc hs hf

/-- Exact count for the full actual mixed quotient sector, with every allowed
positive rescaling and hidden/input permutation restored. -/
theorem mixed_sector_has_32_components :
    Nonempty (ConnectedComponents MixedQuotientSector ≃ Fin 32) :=
  ⟨mixedComponentsEquiv.trans (Fintype.equivFinOfCardEq nonpairedLabel_card)⟩

#print axioms mixedLabel_fiber
#print axioms mixed_sector_has_32_components
end MaxCaterpillar.Fiber.Count65.MixedFullSectorComponents
