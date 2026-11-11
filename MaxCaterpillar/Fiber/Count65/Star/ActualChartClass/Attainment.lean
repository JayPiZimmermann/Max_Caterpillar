import MaxCaterpillar.Fiber.Count65.Star.ActualLabelsPermutation
import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Coverage
import MaxCaterpillar.Fiber.Count65.SectorQuotient.Labels

/-! # All 32 actual star labels have zero-bias physical witnesses

Fixed endpoint charts suffice for this attainment theorem. Every witness is
an ordinary six-array network computing Max4 on all real inputs.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65.StarAttainment
open Set Function Star Star.PhysicalChart ActualStarLabels MaxCaterpillar.Frontier
open MaxCaterpillar.Fiber.Mixed65 (Heads)

noncomputable def endpointI : ResidualBase 0 := ⟨(1,0),by change 0 < (1:ℝ) ∧ 1 ≤ (1:ℝ) ∧ (0:ℝ) ≤ 0; norm_num⟩
noncomputable def endpointII : ResidualBase (-1) := ⟨(1,-1),by change 0 < (1:ℝ) ∧ 1 ≤ (1:ℝ) ∧ (-1:ℝ) ≤ -1; norm_num⟩

noncomputable def remainderI (o : Fin 3 → Bool) : featureSpace 1 :=
  coefficientReadout 1 (branchICoefficients (flipValue (o 0)) (flipValue (o 1))
    (flipValue (o 2)) endpointI)
noncomputable def remainderII (o : Fin 3 → Bool) : featureSpace 1 :=
  coefficientReadout 1 (branchIICoefficients (flipValue (o 0)) (flipValue (o 1))
    (flipValue (o 2)) endpointII)

def headTest (kind : Bool) (D : HeadTopology.Data (featureSpace 1)) : Prop :=
  if kind then ∀ x : InvariantState,
    (HeadTopology.toHeads D).A x+(HeadTopology.toHeads D).B x=0
  else ∀ x : InvariantState,
    0 ≤ (HeadTopology.toHeads D).A x ∧ 0 ≤ (HeadTopology.toHeads D).B x

lemma heads_with_test (L : featureSpace 1) (kind : Bool) :
    ∃ D : HeadTopology.Data (featureSpace 1),
      (HeadTopology.toHeads D).Reconstructs (L : InvariantState → ℝ) ∧ headTest kind D := by
  cases kind
  · obtain ⟨A,B,hA,hB,hAB⟩ := exists_nonnegative_decomposition L.property
    have hAB' : A-B=L := Subtype.ext hAB
    let D := HeadTopology.splitPoint (featureSpace 1) A B
    have hsplit := HeadTopology.splitPoint_isSplit (featureSpace 1) L A B hA hB hAB'
    exact ⟨D,hsplit.reconstructs,fun x => ⟨hA x,hB x⟩⟩
  · let D := HeadTopology.signedPoint (featureSpace 1) L
    have hs : (HeadTopology.toHeads D).IsSigned (L : InvariantState → ℝ) := by
      rw [HeadTopology.toHeads_signedPoint]
      exact Mixed65.signedHeads_isSigned _
    refine ⟨D,hs.reconstructs,?_⟩
    intro x
    rw [hs.1,hs.2.1]
    exact add_neg_self _

noncomputable def fixedSliceI (o : Fin 3 → Bool) (D : HeadTopology.Data (featureSpace 1))
    (hR : (HeadTopology.toHeads D).Reconstructs (remainderI o : InvariantState → ℝ)) : Slice :=
  let q : BranchIFiber o := ⟨(endpointI,D),hR⟩
  ⟨(1,branchIChart o q),by
    refine ⟨by norm_num,le_rfl,rfl,branchIChart_eval o q,?_⟩
    intro i
    fin_cases i <;> norm_num [branchIChart,headLift]⟩
noncomputable def fixedSliceII (o : Fin 3 → Bool) (D : HeadTopology.Data (featureSpace 1))
    (hR : (HeadTopology.toHeads D).Reconstructs (remainderII o : InvariantState → ℝ)) : Slice :=
  let q : BranchIIFiber o := ⟨(endpointII,D),hR⟩
  ⟨(1,branchIIChart o q),by
    refine ⟨by norm_num,le_rfl,rfl,branchIIChart_eval o q,?_⟩
    intro i
    fin_cases i <;> norm_num [branchIIChart,headLift]⟩

lemma headLift_intercept_positive (P Q N : Fin 4 → ℝ)
    (D : HeadTopology.Data (featureSpace 1)) (x : InvariantState) :
    readout 1 ((headLift 1 P Q N D).W₂ 3 0) ((headLift 1 P Q N D).W₂ 3 1)
      ((headLift 1 P Q N D).W₂ 3 2) ((headLift 1 P Q N D).W₂ 3 3) x=
      (HeadTopology.toHeads D).A x := by
  have h := congrFun (congrArg Subtype.val
    (coefficientReadout_recover (by norm_num : (0:ℝ)<1) D.2.1)) x
  simpa only [headLift,extendRow,unscaleCoefficients,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.head_cons,
    Matrix.tail_cons,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,div_one,
    coefficientReadout,HeadTopology.toHeads] using h

lemma headLift_intercept_negative (P Q N : Fin 4 → ℝ)
    (D : HeadTopology.Data (featureSpace 1)) (x : InvariantState) :
    readout 1 ((headLift 1 P Q N D).W₂ 4 0) ((headLift 1 P Q N D).W₂ 4 1)
      ((headLift 1 P Q N D).W₂ 4 2) ((headLift 1 P Q N D).W₂ 4 3) x=
      (HeadTopology.toHeads D).B x := by
  have h := congrFun (congrArg Subtype.val
    (coefficientReadout_recover (by norm_num : (0:ℝ)<1) D.2.2)) x
  simpa only [headLift,extendRow,unscaleCoefficients,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.head_cons,
    Matrix.tail_cons,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,div_one,
    coefficientReadout,HeadTopology.toHeads] using h

lemma fixedSliceI_body (bits : Fin 3 → Bool) (kind : Bool)
    (D : HeadTopology.Data (featureSpace 1))
    (hR : (HeadTopology.toHeads D).Reconstructs (remainderI (chartFlipBits bits) : InvariantState → ℝ)) :
    let p := fixedSliceI (chartFlipBits bits) D hR
    let l : Label := (Equiv.refl (Fin 5),false,bits,kind)
    p ∈ outputClass l ∩ stationaryClass l ∩ orientationClass l ∩ directionClass l := by
  have hc0 : Fin.castAdd 2 (0 : Fin 3)=(0 : Fin 5) := rfl
  have hc1 : Fin.castAdd 2 (1 : Fin 3)=(1 : Fin 5) := rfl
  have hc2 : Fin.castAdd 2 (2 : Fin 3)=(2 : Fin 5) := rfl
  dsimp only
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> exact ⟨rfl,rfl⟩
  · intro i
    fin_cases i <;>
      cases h0 : bits 0 <;> cases h1 : bits 1 <;> cases h2 : bits 2 <;>
      norm_num [orientationClass,core,fixedSliceI,branchIChart,headLift,coreRowsI,
        endpointI,orientedRow,unscaleCoefficients,extendRow,orientation,
        eps,chartFlipBits,coeff,Matrix.vecHead,Matrix.vecTail,rowOrder,orientations,hc0,hc1,hc2,h0,h1,h2] <;> rfl
  · cases h0 : bits 0 <;> cases h1 : bits 1 <;> cases h2 : bits 2 <;>
      norm_num [directionClass,carrierClass,branchClass,core,hValue,kValue,nValue,mValue,
        lValue,normalizedCoeff,fixedSliceI,branchIChart,headLift,coreRowsI,endpointI,
        orientedRow,unscaleCoefficients,extendRow,orientation,eps,chartFlipBits,coeff,time,
        Matrix.vecHead,Matrix.vecTail,rowOrder,branch,orientations,hc0,hc1,hc2,h0,h1,h2] <;> rfl

lemma fixedSliceII_body (bits : Fin 3 → Bool) (kind : Bool)
    (D : HeadTopology.Data (featureSpace 1))
    (hR : (HeadTopology.toHeads D).Reconstructs (remainderII (chartFlipBits bits) : InvariantState → ℝ)) :
    let p := fixedSliceII (chartFlipBits bits) D hR
    let l : Label := (Equiv.refl (Fin 5),true,bits,kind)
    p ∈ outputClass l ∩ stationaryClass l ∩ orientationClass l ∩ directionClass l := by
  have hc0 : Fin.castAdd 2 (0 : Fin 3)=(0 : Fin 5) := rfl
  have hc1 : Fin.castAdd 2 (1 : Fin 3)=(1 : Fin 5) := rfl
  have hc2 : Fin.castAdd 2 (2 : Fin 3)=(2 : Fin 5) := rfl
  dsimp only
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> exact ⟨rfl,rfl⟩
  · intro i
    fin_cases i <;>
      cases h0 : bits 0 <;> cases h1 : bits 1 <;> cases h2 : bits 2 <;>
      norm_num [orientationClass,core,fixedSliceII,branchIIChart,headLift,coreRowsII,
        endpointII,orientedRow,unscaleCoefficients,extendRow,orientation,
        eps,chartFlipBits,coeff,Matrix.vecHead,Matrix.vecTail,rowOrder,orientations,hc0,hc1,hc2,h0,h1,h2] <;> rfl
  · cases h0 : bits 0 <;> cases h1 : bits 1 <;> cases h2 : bits 2 <;>
      norm_num [directionClass,carrierClass,branchClass,core,hValue,kValue,nValue,mValue,
        lValue,normalizedCoeff,fixedSliceII,branchIIChart,headLift,coreRowsII,endpointII,
        orientedRow,unscaleCoefficients,extendRow,orientation,eps,chartFlipBits,coeff,time,
        Matrix.vecHead,Matrix.vecTail,rowOrder,branch,orientations,hc0,hc1,hc2,h0,h1,h2] <;> rfl

lemma fixedSliceI_class (bits : Fin 3 → Bool) (kind : Bool)
    (D : HeadTopology.Data (featureSpace 1))
    (hR : (HeadTopology.toHeads D).Reconstructs (remainderI (chartFlipBits bits) : InvariantState → ℝ))
    (hT : headTest kind D) :
    fixedSliceI (chartFlipBits bits) D hR ∈
      physicalClass (Equiv.refl (Fin 5),false,bits,kind) := by
  refine ⟨fixedSliceI_body bits kind D hR,?_⟩
  have hA (x : InvariantState) : intercept (fixedSliceI (chartFlipBits bits) D hR) 3 x=
      (HeadTopology.toHeads D).A x := headLift_intercept_positive _ _ _ D x
  have hB (x : InvariantState) : intercept (fixedSliceI (chartFlipBits bits) D hR) 4 x=
      (HeadTopology.toHeads D).B x := headLift_intercept_negative _ _ _ D x
  cases kind
  · intro x
    change 0 ≤ intercept (fixedSliceI (chartFlipBits bits) D hR) 3 x ∧
      0 ≤ intercept (fixedSliceI (chartFlipBits bits) D hR) 4 x
    rw [hA,hB]
    exact hT x
  · intro x
    change intercept (fixedSliceI (chartFlipBits bits) D hR) 3 x+
      intercept (fixedSliceI (chartFlipBits bits) D hR) 4 x=0
    rw [hA,hB]
    exact hT x

lemma fixedSliceII_class (bits : Fin 3 → Bool) (kind : Bool)
    (D : HeadTopology.Data (featureSpace 1))
    (hR : (HeadTopology.toHeads D).Reconstructs (remainderII (chartFlipBits bits) : InvariantState → ℝ))
    (hT : headTest kind D) :
    fixedSliceII (chartFlipBits bits) D hR ∈
      physicalClass (Equiv.refl (Fin 5),true,bits,kind) := by
  refine ⟨fixedSliceII_body bits kind D hR,?_⟩
  have hA (x : InvariantState) : intercept (fixedSliceII (chartFlipBits bits) D hR) 3 x=
      (HeadTopology.toHeads D).A x := headLift_intercept_positive _ _ _ D x
  have hB (x : InvariantState) : intercept (fixedSliceII (chartFlipBits bits) D hR) 4 x=
      (HeadTopology.toHeads D).B x := headLift_intercept_negative _ _ _ D x
  cases kind
  · intro x
    change 0 ≤ intercept (fixedSliceII (chartFlipBits bits) D hR) 3 x ∧
      0 ≤ intercept (fixedSliceII (chartFlipBits bits) D hR) 4 x
    rw [hA,hB]
    exact hT x
  · intro x
    change intercept (fixedSliceII (chartFlipBits bits) D hR) 3 x+
      intercept (fixedSliceII (chartFlipBits bits) D hR) 4 x=0
    rw [hA,hB]
    exact hT x

/-- Every one of the 32 star labels has an actual zero-bias physical witness. -/
theorem all_labels_attained (l : NonpairedLabel) :
    ∃ p : Slice,p.val.2.HasZeroBiases ∧ componentLabel p=l := by
  rcases l with ⟨b,bits,kind⟩
  cases b
  · obtain ⟨D,hR,hT⟩ := heads_with_test (remainderI (chartFlipBits bits)) kind
    let p := fixedSliceI (chartFlipBits bits) D hR
    have hc := fixedSliceI_class bits kind D hR hT
    have hl := (actualLabel_eq_iff p (Equiv.refl (Fin 5),false,bits,kind)).mpr hc
    refine ⟨p,⟨rfl,rfl,rfl⟩,?_⟩
    unfold componentLabel
    rw [hl]
  · obtain ⟨D,hR,hT⟩ := heads_with_test (remainderII (chartFlipBits bits)) kind
    let p := fixedSliceII (chartFlipBits bits) D hR
    have hc := fixedSliceII_class bits kind D hR hT
    have hl := (actualLabel_eq_iff p (Equiv.refl (Fin 5),true,bits,kind)).mpr hc
    refine ⟨p,⟨rfl,rfl,rfl⟩,?_⟩
    unfold componentLabel
    rw [hl]

/-- Attainment survives in the genuine zero-bias full symmetry quotient. -/
theorem starZeroBiasLabel_attained (l : NonpairedLabel) :
    ∃ z : ZeroBiasSymmetryQuotient 4 6 5,SectorQuotient.starZeroBiasLabel z=some l := by
  obtain ⟨p,hz,hp⟩ := all_labels_attained l
  refine ⟨Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
    (⟨SectorQuotient.canonicalStarFiber p,hz⟩ : ZeroBiasFiber 4 6 5),?_⟩
  rw [SectorQuotient.starZeroBiasLabel_canonical p hz,hp]

#check @all_labels_attained
#check @starZeroBiasLabel_attained
#print axioms all_labels_attained
#print axioms starZeroBiasLabel_attained
end MaxCaterpillar.Fiber.Count65.StarAttainment
