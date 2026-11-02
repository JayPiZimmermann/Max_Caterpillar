import MaxCaterpillar.Fiber.Count65.Star.ActualChartClass.Base

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualStarLabels
open Set Function Star Star65 Star.PhysicalChart MaxCaterpillar.Frontier

lemma eps_square (bits : Fin 3 → Bool) (i : Fin 3) : eps bits i*eps bits i=1 := by
  unfold eps
  split_ifs <;> norm_num
lemma orientation_chartFlipBits (bits : Fin 3 → Bool) (i : Fin 3) :
    orientation (chartFlipBits bits i) = -eps bits i := by
  unfold chartFlipBits eps
  cases bits i <;> norm_num [orientation]

private lemma extendRow_firstFour (c : Fin 4 → ℝ) (a b : ℝ) (j : Fin 4) :
    extendRow c a b (Fin.castAdd 2 j)=c j := by fin_cases j <;> rfl

lemma chartI_core_coefficient (bits : Fin 3 → Bool) (q : ChartI bits)
    (i : Fin 3) (j : Fin 4) :
    coeff (chartI bits q) (Fin.castAdd 2 i) (Fin.castAdd 2 j)=
      orientation (chartFlipBits bits i)*branchIRows q.val.1.val.1 q.val.1.val.2 i j := by
  have he : (branchIChart (chartFlipBits bits) q).W₂ (Fin.castAdd 2 i)=
      extendRow (unscaleCoefficients q.val.1.val.1
        (orientedRow (chartFlipBits bits i) (coreRowsI q.val.1 i))) 0 0 := by
    fin_cases i <;> rfl
  change (branchIChart (chartFlipBits bits) q).W₂ (Fin.castAdd 2 i) (Fin.castAdd 2 j)=_
  rw [he,extendRow_firstFour,unscale_orientedRow,← branchIRows_eq_unscale]

lemma chartII_core_coefficient (bits : Fin 3 → Bool) (q : ChartII bits)
    (i : Fin 3) (j : Fin 4) :
    coeff (chartII bits q) (Fin.castAdd 2 i) (Fin.castAdd 2 j)=
      orientation (chartFlipBits bits i)*branchIIRows q.val.1.val.1 q.val.1.val.2 i j := by
  have he : (branchIIChart (chartFlipBits bits) q).W₂ (Fin.castAdd 2 i)=
      extendRow (unscaleCoefficients q.val.1.val.1
        (orientedRow (chartFlipBits bits i) (coreRowsII q.val.1 i))) 0 0 := by
    fin_cases i <;> rfl
  change (branchIIChart (chartFlipBits bits) q).W₂ (Fin.castAdd 2 i) (Fin.castAdd 2 j)=_
  rw [he,extendRow_firstFour,unscale_orientedRow,← branchIIRows_eq_unscale]

lemma normalizedCoeff_chartI (bits : Fin 3 → Bool) (q : ChartI bits)
    (b kind : Bool) (i : Fin 3) (j : Fin 4) :
    normalizedCoeff (Equiv.refl (Fin 5),b,bits,kind) (chartI bits q) i (Fin.castAdd 2 j)=
      branchIRows q.val.1.val.1 q.val.1.val.2 i j := by
  change -eps bits i*coeff (chartI bits q) (Fin.castAdd 2 i) (Fin.castAdd 2 j)=_
  rw [chartI_core_coefficient,orientation_chartFlipBits]
  calc
    -eps bits i*(-eps bits i*branchIRows q.val.1.val.1 q.val.1.val.2 i j)=
      (eps bits i*eps bits i)*branchIRows q.val.1.val.1 q.val.1.val.2 i j := by ring
    _ = _ := by rw [eps_square,one_mul]

lemma normalizedCoeff_chartII (bits : Fin 3 → Bool) (q : ChartII bits)
    (b kind : Bool) (i : Fin 3) (j : Fin 4) :
    normalizedCoeff (Equiv.refl (Fin 5),b,bits,kind) (chartII bits q) i (Fin.castAdd 2 j)=
      branchIIRows q.val.1.val.1 q.val.1.val.2 i j := by
  change -eps bits i*coeff (chartII bits q) (Fin.castAdd 2 i) (Fin.castAdd 2 j)=_
  rw [chartII_core_coefficient,orientation_chartFlipBits]
  calc
    -eps bits i*(-eps bits i*branchIIRows q.val.1.val.1 q.val.1.val.2 i j)=
      (eps bits i*eps bits i)*branchIIRows q.val.1.val.1 q.val.1.val.2 i j := by ring
    _ = _ := by rw [eps_square,one_mul]

lemma chartI_intercept_positive (bits : Fin 3 → Bool) (q : ChartI bits) (x : InvariantState) :
    intercept (chartI bits q) 3 x=
      (HeadTopology.toHeads q.val.2).A (x.1/q.val.1.val.1,x.2.1,x.2.2) := by
  change starLinearForm q.val.1.val.1
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.1) 0)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.1) 1)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.1) 2)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.1) 3) x.1 x.2.1 x.2.2=_
  rw [unscaleCoefficients_readout q.val.1.property.1]
  exact congrFun (congrArg Subtype.val (coefficientReadout_recover
    (by norm_num : 0 < (1 : ℝ)) q.val.2.2.1)) _
lemma chartI_intercept_negative (bits : Fin 3 → Bool) (q : ChartI bits) (x : InvariantState) :
    intercept (chartI bits q) 4 x=
      (HeadTopology.toHeads q.val.2).B (x.1/q.val.1.val.1,x.2.1,x.2.2) := by
  change starLinearForm q.val.1.val.1
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.2) 0)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.2) 1)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.2) 2)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.2) 3) x.1 x.2.1 x.2.2=_
  rw [unscaleCoefficients_readout q.val.1.property.1]
  exact congrFun (congrArg Subtype.val (coefficientReadout_recover
    (by norm_num : 0 < (1 : ℝ)) q.val.2.2.2)) _
lemma chartII_intercept_positive (bits : Fin 3 → Bool) (q : ChartII bits) (x : InvariantState) :
    intercept (chartII bits q) 3 x=
      (HeadTopology.toHeads q.val.2).A (x.1/q.val.1.val.1,x.2.1,x.2.2) := by
  change starLinearForm q.val.1.val.1
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.1) 0)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.1) 1)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.1) 2)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.1) 3) x.1 x.2.1 x.2.2=_
  rw [unscaleCoefficients_readout q.val.1.property.1]
  exact congrFun (congrArg Subtype.val (coefficientReadout_recover
    (by norm_num : 0 < (1 : ℝ)) q.val.2.2.1)) _
lemma chartII_intercept_negative (bits : Fin 3 → Bool) (q : ChartII bits) (x : InvariantState) :
    intercept (chartII bits q) 4 x=
      (HeadTopology.toHeads q.val.2).B (x.1/q.val.1.val.1,x.2.1,x.2.2) := by
  change starLinearForm q.val.1.val.1
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.2) 0)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.2) 1)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.2) 2)
    (unscaleCoefficients q.val.1.val.1 (recoverReadout 1 q.val.2.2.2) 3) x.1 x.2.1 x.2.2=_
  rw [unscaleCoefficients_readout q.val.1.property.1]
  exact congrFun (congrArg Subtype.val (coefficientReadout_recover
    (by norm_num : 0 < (1 : ℝ)) q.val.2.2.2)) _

end MaxCaterpillar.Fiber.Count65.ActualStarLabels
