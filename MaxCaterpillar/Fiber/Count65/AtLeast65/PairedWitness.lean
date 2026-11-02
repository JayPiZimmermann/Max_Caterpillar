import MaxCaterpillar.Fiber.Count65.SectorQuotient.Labels

/-! A concrete actual zero-bias quotient point in the paired sector. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.AtLeast65

open SectorQuotient

lemma paddedMinimalPoint_zeroBias : Mixed65.paddedMinimalPoint.val.HasZeroBiases :=
  (Network.padSecond_props 2 Frontier.maxFourNet).2 Frontier.maxFourNet_hasZeroBiases

lemma paddedMinimalPoint_paired : PairedFirstMatrixForm Mixed65.paddedMinimalPoint.val := by
  have hw : Mixed65.paddedMinimalPoint.val.W₁ = pairedRows 1 0 0 1 := by
    change Frontier.maxFourNet.W₁ = pairedRows 1 0 0 1
    simp only [Frontier.maxFourNet,pairedRows,neg_zero]
  refine ⟨1,0,0,1,by norm_num,(fun _ => 1),(fun _ => zero_lt_one),
    Equiv.refl _,Equiv.refl _,?_⟩
  intro j i
  simp only [Equiv.refl_apply,one_mul,hw]

noncomputable def pairedWitnessZeroPoint : ZeroBiasFiber 4 6 5 :=
  ⟨Mixed65.paddedMinimalPoint,paddedMinimalPoint_zeroBias⟩

noncomputable def pairedWitness : ZeroBiasSymmetryQuotient 4 6 5 :=
  Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) pairedWitnessZeroPoint

lemma pairedWitness_mixedLabel : mixedZeroBiasLabel pairedWitness=none := by
  apply (mixedZeroBiasLabel_none_iff pairedWitnessZeroPoint).mpr
  intro hm
  exact not_paired_of_mixedFirstMatrixForm Mixed65.paddedMinimalPoint.val
    ((Mixed65.mem_sector_iff_firstMatrixForm Mixed65.paddedMinimalPoint).mp hm)
    paddedMinimalPoint_paired

lemma pairedWitness_starLabel : starZeroBiasLabel pairedWitness=none := by
  apply (starZeroBiasLabel_none_iff pairedWitnessZeroPoint).mpr
  intro hs
  exact not_paired_of_starFirstMatrixForm Mixed65.paddedMinimalPoint.val hs
    paddedMinimalPoint_paired

end MaxCaterpillar.Fiber.Count65.AtLeast65
