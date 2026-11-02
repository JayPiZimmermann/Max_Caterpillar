import MaxCaterpillar.Fiber.Count65.SectorQuotient

set_option autoImplicit false
noncomputable section
open MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.Count65
open MaxCaterpillar.Fiber.Count65.SectorQuotient

/-- The codomain has the ordinary discrete finite topology. -/
example : optionNonpairedLabelTopology=(⊥ : TopologicalSpace (Option NonpairedLabel)) := rfl

/-- Full genuine orbits between canonical unit-output frames leave exactly
the second hidden-neuron names free, including the star endpoint. -/
example (a b : ExactFiber 4 6 5) (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (ha : a.val.W₁=Mixed65.firstRows t) (hb : b.val.W₁=Mixed65.firstRows u)
    (haunit : ∀ k,a.val.w₃ k=1 ∨ a.val.w₃ k = -1)
    (hbunit : ∀ k,b.val.w₃ k=1 ∨ b.val.w₃ k = -1) :
    (symmetrySetoid 4 6 5).r a b ↔
      t=u ∧ ∃ p : Equiv.Perm (Fin 5),b.val=permuteHidden a.val (Equiv.refl _) p :=
  mixed_normalized_symmetry_iff a b t u ht hu ha hb haunit hbunit

example (a b : ExactFiber 4 6 5) (t u : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hu : 0<u) (hu1 : u≤1)
    (ha : a.val.W₁=Star65.firstRows t) (hb : b.val.W₁=Star65.firstRows u)
    (haunit : ∀ k,a.val.w₃ k=1 ∨ a.val.w₃ k = -1)
    (hbunit : ∀ k,b.val.w₃ k=1 ∨ b.val.w₃ k = -1) :
    (symmetrySetoid 4 6 5).r a b ↔
      t=u ∧ ∃ p : Equiv.Perm (Fin 5),b.val=permuteHidden a.val (Equiv.refl _) p :=
  star_normalized_symmetry_iff a b t u ht ht1 hu hu1 ha hb haunit hbunit

/-- The maps live on the genuine symmetry quotient, restricted only to zero
biases. Their equivalence relation is exactly the comap of generated physical
symmetries, rather than an invented normal-form identification. -/
example : Continuous (mixedZeroBiasLabel :
    Quotient (Setoid.comap (Subtype.val : ZeroBiasFiber 4 6 5 → ExactFiber 4 6 5)
      (symmetrySetoid 4 6 5)) → Option NonpairedLabel) := continuous_mixedZeroBiasLabel
example : Continuous (starZeroBiasLabel :
    Quotient (Setoid.comap (Subtype.val : ZeroBiasFiber 4 6 5 → ExactFiber 4 6 5)
      (symmetrySetoid 4 6 5)) → Option NonpairedLabel) := continuous_starZeroBiasLabel

example (p : ActualMixedLabels.Slice) (hz : p.val.2.HasZeroBiases) :
    mixedZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
      (⟨canonicalMixedFiber p,hz⟩ : ZeroBiasFiber 4 6 5))=
      some (ActualMixedLabels.componentLabel p) := mixedZeroBiasLabel_canonical p hz
example (p : ActualStarLabels.Slice) (hz : p.val.2.HasZeroBiases) :
    starZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
      (⟨canonicalStarFiber p,hz⟩ : ZeroBiasFiber 4 6 5))=
      some (ActualStarLabels.componentLabel p) := starZeroBiasLabel_canonical p hz

example (z : ZeroBiasSymmetryQuotient 4 6 5) (l : NonpairedLabel)
    (h : mixedZeroBiasLabel z=some l) :
    ∃ (p : ActualMixedLabels.Slice) (hz : p.val.2.HasZeroBiases),
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
        (⟨canonicalMixedFiber p,hz⟩ : ZeroBiasFiber 4 6 5)=z ∧
      ActualMixedLabels.componentLabel p=l := mixedZeroBiasLabel_some_covered z l h
example (z : ZeroBiasSymmetryQuotient 4 6 5) (l : NonpairedLabel)
    (h : starZeroBiasLabel z=some l) :
    ∃ (p : ActualStarLabels.Slice) (hz : p.val.2.HasZeroBiases),
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
        (⟨canonicalStarFiber p,hz⟩ : ZeroBiasFiber 4 6 5)=z ∧
      ActualStarLabels.componentLabel p=l := starZeroBiasLabel_some_covered z l h

example (x : ZeroBiasFiber 4 6 5) :
    mixedZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x)=none ↔
      includeZeroBias x∉Mixed65.sector := mixedZeroBiasLabel_none_iff x
example (x : ZeroBiasFiber 4 6 5) :
    starZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x)=none ↔
      includeZeroBias x∉starSet := starZeroBiasLabel_none_iff x

#print axioms mixed_normalized_symmetry_iff
#print axioms star_normalized_symmetry_iff
#print axioms pairedSector_isClopen
#print axioms starSector_isClopen
#print axioms continuous_mixedZeroBiasLabel
#print axioms continuous_starZeroBiasLabel
#print axioms mixedZeroBiasLabel_canonical
#print axioms starZeroBiasLabel_canonical
#print axioms mixedZeroBiasLabel_some_covered
#print axioms starZeroBiasLabel_some_covered
#print axioms continuous_mixedFullLabel
#print axioms continuous_starFullLabel
