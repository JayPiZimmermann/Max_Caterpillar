import MaxCaterpillar.Fiber.Count65.SectorQuotient.ActualAtlases
import MaxCaterpillar.Fiber.Count65.SectorQuotient.ExtendedLabel

/-! Concrete continuous mixed and star labels on the genuine full and zero-bias
symmetry quotients. A some-label always has an actual canonical representative
of that same quotient point, with zero biases preserved. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

lemma canonicalMixedFiber_mem_sector (p : ActualMixedLabels.Slice) :
    canonicalMixedFiber p ∈ Mixed65.sector := by
  apply (Mixed65.mem_sector_iff_firstMatrixForm _).mpr
  refine ⟨p.val.1,p.property.1,(fun _ => 1),(fun _ => zero_lt_one),
    Equiv.refl _,Equiv.refl _,?_⟩
  intro j i
  change p.val.2.W₁ j i = 1 * Mixed65.firstRows p.val.1 j i
  rw [p.property.2.1,one_mul]

lemma canonicalStarFiber_mem_starSet (p : ActualStarLabels.Slice) :
    canonicalStarFiber p ∈ starSet := by
  refine ⟨p.val.1,p.property.1,p.property.2.1,(fun _ => 1),(fun _ => zero_lt_one),
    Equiv.refl _,Equiv.refl _,?_⟩
  intro j i
  change p.val.2.W₁ j i = 1 * Star65.firstRows p.val.1 j i
  rw [p.property.2.2.1,one_mul]

noncomputable def mixedZeroBiasLabel :
    ZeroBiasSymmetryQuotient 4 6 5 → Option NonpairedLabel :=
  mixedAtlas.zeroBiasQuotientLabel Mixed65.sector_invariant

noncomputable def starZeroBiasLabel :
    ZeroBiasSymmetryQuotient 4 6 5 → Option NonpairedLabel :=
  starAtlas.zeroBiasQuotientLabel starSet_symmetryInvariant

lemma continuous_mixedZeroBiasLabel : Continuous mixedZeroBiasLabel :=
  mixedAtlas.continuous_zeroBiasQuotientLabel
    max4_6_5_mixed_sector_isClopen Mixed65.sector_invariant

lemma continuous_starZeroBiasLabel : Continuous starZeroBiasLabel :=
  starAtlas.continuous_zeroBiasQuotientLabel starSector_isClopen starSet_symmetryInvariant

lemma mixedZeroBiasLabel_mk (x : ZeroBiasFiber 4 6 5) :
    mixedZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x)=
      mixedAtlas.extendedLabel (includeZeroBias x) := rfl

lemma starZeroBiasLabel_mk (x : ZeroBiasFiber 4 6 5) :
    starZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x)=
      starAtlas.extendedLabel (includeZeroBias x) := rfl

lemma mixedZeroBiasLabel_none_iff (x : ZeroBiasFiber 4 6 5) :
    mixedZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x)=none ↔
      includeZeroBias x ∉ Mixed65.sector :=
  mixedAtlas.extendedLabel_none_iff (includeZeroBias x)

lemma starZeroBiasLabel_none_iff (x : ZeroBiasFiber 4 6 5) :
    starZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x)=none ↔
      includeZeroBias x ∉ starSet :=
  starAtlas.extendedLabel_none_iff (includeZeroBias x)

lemma mixedZeroBiasLabel_canonical (p : ActualMixedLabels.Slice)
    (hz : p.val.2.HasZeroBiases) :
    mixedZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
      (⟨canonicalMixedFiber p,hz⟩ : ZeroBiasFiber 4 6 5))=
      some (ActualMixedLabels.componentLabel p) :=
  mixedAtlas.zeroBiasQuotientLabel_canonical Mixed65.sector_invariant p
    (canonicalMixedFiber_mem_sector p) hz

lemma starZeroBiasLabel_canonical (p : ActualStarLabels.Slice)
    (hz : p.val.2.HasZeroBiases) :
    starZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
      (⟨canonicalStarFiber p,hz⟩ : ZeroBiasFiber 4 6 5))=
      some (ActualStarLabels.componentLabel p) :=
  starAtlas.zeroBiasQuotientLabel_canonical starSet_symmetryInvariant p
    (canonicalStarFiber_mem_starSet p) hz

/-- A mixed some-label supplies an actual canonical zero-bias network in the
same genuine symmetry quotient, rather than a separately identified normal form. -/
theorem mixedZeroBiasLabel_some_covered (z : ZeroBiasSymmetryQuotient 4 6 5)
    (l : NonpairedLabel) (h : mixedZeroBiasLabel z=some l) :
    ∃ (p : ActualMixedLabels.Slice) (hz : p.val.2.HasZeroBiases),
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
        (⟨canonicalMixedFiber p,hz⟩ : ZeroBiasFiber 4 6 5)=z ∧
      ActualMixedLabels.componentLabel p=l :=
  mixedAtlas.zeroBiasQuotientLabel_some_covered Mixed65.sector_invariant z l h

/-- The same actual-representative statement holds at every star parameter,
including the endpoint one. -/
theorem starZeroBiasLabel_some_covered (z : ZeroBiasSymmetryQuotient 4 6 5)
    (l : NonpairedLabel) (h : starZeroBiasLabel z=some l) :
    ∃ (p : ActualStarLabels.Slice) (hz : p.val.2.HasZeroBiases),
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
        (⟨canonicalStarFiber p,hz⟩ : ZeroBiasFiber 4 6 5)=z ∧
      ActualStarLabels.componentLabel p=l :=
  starAtlas.zeroBiasQuotientLabel_some_covered starSet_symmetryInvariant z l h

noncomputable def mixedFullLabel : SymmetryQuotient 4 6 5 → Option NonpairedLabel :=
  mixedAtlas.fullQuotientLabel Mixed65.sector_invariant
noncomputable def starFullLabel : SymmetryQuotient 4 6 5 → Option NonpairedLabel :=
  starAtlas.fullQuotientLabel starSet_symmetryInvariant

lemma continuous_mixedFullLabel : Continuous mixedFullLabel :=
  mixedAtlas.continuous_fullQuotientLabel max4_6_5_mixed_sector_isClopen Mixed65.sector_invariant
lemma continuous_starFullLabel : Continuous starFullLabel :=
  starAtlas.continuous_fullQuotientLabel starSector_isClopen starSet_symmetryInvariant

lemma mixedFullLabel_mk (x : ExactFiber 4 6 5) :
    mixedFullLabel (quotientMk x)=mixedAtlas.extendedLabel x := rfl
lemma starFullLabel_mk (x : ExactFiber 4 6 5) :
    starFullLabel (quotientMk x)=starAtlas.extendedLabel x := rfl

end MaxCaterpillar.Fiber.Count65.SectorQuotient
