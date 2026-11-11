import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsExhaustion
import MaxCaterpillar.Fiber.Count65.Mixed.PhysicalChart

/-! # Actual mixed physical networks are covered by the continuous charts

The reconstruction below matches all network arrays after a genuine hidden
permutation. Equality of evaluations is used to recover the exact head-fiber
condition, rather than added as an extra symmetry.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65.ActualMixedLabels
open Set Function Mixed65 MaxCaterpillar.Frontier

noncomputable def originalHeadCoefficients (p : Slice) (i : Fin 5) : Fin 4 → ℝ :=
  fun j => coeff p i (Fin.castAdd 2 j)

noncomputable def fixedHeadCoefficients (p : Slice) (i : Fin 5) : Fin 4 → ℝ :=
  ![coeff p i 0/time p,coeff p i 1,coeff p i 2,coeff p i 3]

noncomputable def headSlopes (p : Slice) (e : Equiv.Perm (Fin 5)) : Fin 4 → ℝ :=
  ![coeff p (e 3) 4,coeff p (e 3) 5,coeff p (e 4) 4,coeff p (e 4) 5]

lemma varying_fixedHeadCoefficients (p : Slice) (i : Fin 5) :
    varyingCoefficients (time p) (fixedHeadCoefficients p i)=originalHeadCoefficients p i := by
  have ht : time p ≠ 0 := ne_of_gt p.property.1
  funext j
  fin_cases j
  · change time p*(coeff p i 0/time p)=coeff p i 0
    field_simp [ht]
    ring
  all_goals rfl

/-- Reordering the actual five rows recovers a physical lift literally,
including all its zero bias arrays and stationary translation coefficients. -/
lemma permute_eq_actualLift (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (hz : p.val.2.HasZeroBiases) :
    permuteHidden p.val.2 (Equiv.refl _) (rowOrder l) =
      residualLift (time p) (core p (rowOrder l)) (headSlopes p (rowOrder l))
        (originalHeadCoefficients p (rowOrder l 3))
        (originalHeadCoefficients p (rowOrder l 4)) := by
  have ho := hl.1.1.1.1
  have hs := hl.1.1.1.2
  apply (networkEquivParameters 4 6 5).injective
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))))
  · exact p.property.2.1
  · exact hz.1
  · change (permuteHidden p.val.2 (Equiv.refl _) (rowOrder l)).W₂ = _
    funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [permuteHidden,residualLift,core,headSlopes,originalHeadCoefficients]
    all_goals first
      | exact (hs 0).1
      | exact (hs 0).2
      | exact (hs 1).1
      | exact (hs 1).2
      | exact (hs 2).1
      | exact (hs 2).2
      | rfl
  · funext i
    change p.val.2.b₂ (rowOrder l i)=0
    rw [hz.2.1]
    rfl
  · change (permuteHidden p.val.2 (Equiv.refl _) (rowOrder l)).w₃ = _
    funext i
    fin_cases i <;> norm_num [permuteHidden,residualLift,core,networkEquivParameters]
    all_goals first | rfl | exact ho 3 | exact ho 4
  · exact hz.2.2

lemma residualLift_congr_fields (t : ℝ) (d f : ResidualSystem (Fin 3))
    (s A B : Fin 4 → ℝ) (hU : d.U=f.U) (hV : d.V=f.V)
    (hW : d.W=f.W) (hT : d.T=f.T) (ho : d.out=f.out) :
    residualLift t d s A B=residualLift t f s A B := by
  unfold residualLift
  rw [hU,hV,hW,hT,ho]

/-- Exact physical evaluation determines the complete head reconstruction
identity once the actual residual lift is known. -/
lemma residualLift_heads_of_exact (t : ℝ) (d : ResidualSystem (Fin 3))
    (s A B : Fin 4 → ℝ) (hd : d.Represents t)
    (he : ∀ y,(residualLift t d s A B).eval y=Maximum 4 y) :
    (coefficientHeads t s A B).Reconstructs
      (fun x => d.base t x.1 x.2.1 x.2.2) := by
  intro x z
  have hh := residualLift_eval t d s A B (translatedInput x z)
  rw [he,maximum_translatedInput] at hh
  have hq : translatedInput x z 0-translatedInput x z 1=x.1 := by
    norm_num [translatedInput] <;> ring
  have hb : translatedInput x z 1-translatedInput x z 2=x.2.1 := by
    norm_num [translatedInput] <;> ring
  have hc : translatedInput x z 3-translatedInput x z 2=x.2.2 := by
    norm_num [translatedInput] <;> ring
  have hz : translatedInput x z 2=z := rfl
  rw [hq,hb,hc,hz] at hh
  have hr := hd x.1 x.2.1 x.2.2
  change _=z+_
  dsimp only [invariantTarget] at hh
  linarith only [hh,hr]

lemma orientation_coefficient (bits : Fin 3 → Bool) (i : Fin 3) (c w y : ℝ)
    (hw : w=eps bits i) (hy : y=c*w) : (if bits i then -c else c)=y := by
  rw [hy,hw]
  unfold eps
  split_ifs <;> ring

lemma canonicalResidualA_fields (d : ResidualSystem (Fin 3)) (t k : ℝ)
    (bits : Fin 3 → Bool) (hd : d.HasADirections t k)
    (hw : ∀ i,d.W i=eps bits i) (ho : d.out = ![1,1,-1]) :
    ((canonicalResidualA t k).flip bits).U=d.U ∧
    ((canonicalResidualA t k).flip bits).V=d.V ∧
    ((canonicalResidualA t k).flip bits).W=d.W ∧
    ((canonicalResidualA t k).flip bits).T=d.T ∧
    ((canonicalResidualA t k).flip bits).out=d.out := by
  rcases hd with ⟨hu0,hv0,ht0,hu1,hv1,ht1,hu2,hv2,ht2⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · funext i
    fin_cases i
    · change (if bits 0 then -(-(1+t)) else -(1+t))=d.U 0
      exact orientation_coefficient bits 0 _ _ _ (hw 0) hu0
    · change (if bits 1 then -(-1 : ℝ) else -1)=d.U 1
      exact orientation_coefficient bits 1 _ _ _ (hw 1) (by simpa only [neg_one_mul] using hu1)
    · change (if bits 2 then -(-(1+t)) else -(1+t))=d.U 2
      exact orientation_coefficient bits 2 _ _ _ (hw 2) hu2
  · funext i
    fin_cases i
    · change (if bits 0 then -(0 : ℝ) else 0)=d.V 0
      exact orientation_coefficient bits 0 _ _ _ (hw 0) (by simpa only [zero_mul] using hv0)
    · change (if bits 1 then -(-1 : ℝ) else -1)=d.V 1
      exact orientation_coefficient bits 1 _ _ _ (hw 1) (by simpa only [neg_one_mul] using hv1)
    · change (if bits 2 then -(0 : ℝ) else 0)=d.V 2
      exact orientation_coefficient bits 2 _ _ _ (hw 2) (by simpa only [zero_mul] using hv2)
  · funext i
    fin_cases i
    · exact (hw 0).symm
    · exact (hw 1).symm
    · exact (hw 2).symm
  · funext i
    fin_cases i
    · change (if bits 0 then -(1 : ℝ) else 1)=d.T 0
      exact orientation_coefficient bits 0 _ _ _ (hw 0) (by simpa only [one_mul] using ht0)
    · change (if bits 1 then -k else k)=d.T 1
      exact orientation_coefficient bits 1 _ _ _ (hw 1) ht1
    · change (if bits 2 then -(k+1) else k+1)=d.T 2
      exact orientation_coefficient bits 2 _ _ _ (hw 2) ht2
  · exact ho.symm

lemma canonicalResidualB_fields (d : ResidualSystem (Fin 3)) (t v : ℝ)
    (bits : Fin 3 → Bool) (hd : d.HasBDirections t v)
    (hw : ∀ i,d.W i=eps bits i) (ho : d.out = ![1,1,-1]) :
    ((canonicalResidualB t v).flip bits).U=d.U ∧
    ((canonicalResidualB t v).flip bits).V=d.V ∧
    ((canonicalResidualB t v).flip bits).W=d.W ∧
    ((canonicalResidualB t v).flip bits).T=d.T ∧
    ((canonicalResidualB t v).flip bits).out=d.out := by
  rcases hd with ⟨hu0,hv0,ht0,hu1,hv1,ht1,hu2,hv2,ht2⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · funext i
    fin_cases i
    · change (if bits 0 then -(-(1+t)) else -(1+t))=d.U 0
      exact orientation_coefficient bits 0 _ _ _ (hw 0) hu0
    · change (if bits 1 then -(-1 : ℝ) else -1)=d.U 1
      exact orientation_coefficient bits 1 _ _ _ (hw 1) (by simpa only [neg_one_mul] using hu1)
    · change (if bits 2 then -(-1 : ℝ) else -1)=d.U 2
      exact orientation_coefficient bits 2 _ _ _ (hw 2) (by simpa only [neg_one_mul] using hu2)
  · funext i
    fin_cases i
    · change (if bits 0 then -v else v)=d.V 0
      exact orientation_coefficient bits 0 _ _ _ (hw 0) hv0
    · change (if bits 1 then -(-1 : ℝ) else -1)=d.V 1
      exact orientation_coefficient bits 1 _ _ _ (hw 1) (by simpa only [neg_one_mul] using hv1)
    · change (if bits 2 then -(v-1) else v-1)=d.V 2
      exact orientation_coefficient bits 2 _ _ _ (hw 2) hv2
  · funext i
    fin_cases i
    · exact (hw 0).symm
    · exact (hw 1).symm
    · exact (hw 2).symm
  · funext i
    fin_cases i
    · change (if bits 0 then -(1 : ℝ) else 1)=d.T 0
      exact orientation_coefficient bits 0 _ _ _ (hw 0) (by simpa only [one_mul] using ht0)
    · change (if bits 1 then -(0 : ℝ) else 0)=d.T 1
      exact orientation_coefficient bits 1 _ _ _ (hw 1) (by simpa only [zero_mul] using ht1)
    · change (if bits 2 then -(0 : ℝ) else 0)=d.T 2
      exact orientation_coefficient bits 2 _ _ _ (hw 2) (by simpa only [zero_mul] using ht2)
  · exact ho.symm

noncomputable def extractedBaseA (p : Slice) (k : ℝ) (hk : 1 ≤ time p*k) :
    ResidualChartBase := (⟨time p,p.property.1⟩,⟨time p*k-1,by linarith only [hk]⟩)
noncomputable def extractedBaseB (p : Slice) (v : ℝ) (hv : 1+time p ≤ time p*v) :
    ResidualChartBase := (⟨time p,p.property.1⟩,⟨time p*v-1-time p,by linarith only [hv]⟩)

lemma chartK_extractedBaseA (p : Slice) (k : ℝ) (hk : 1 ≤ time p*k) :
    chartK (extractedBaseA p k hk)=k := by
  have ht : time p ≠ 0 := ne_of_gt p.property.1
  dsimp only [chartK,extractedBaseA]
  field_simp [ht]
  ring
lemma chartR_extractedBaseB (p : Slice) (v : ℝ) (hv : 1+time p ≤ time p*v) :
    chartR (extractedBaseB p v hv)=v := by
  have ht : time p ≠ 0 := ne_of_gt p.property.1
  dsimp only [chartR,extractedBaseB]
  field_simp [ht]
  ring

noncomputable def actualHeadData (p : Slice) (e : Equiv.Perm (Fin 5)) :
    HeadTopology.Data (featureSpace 1) :=
  (headSlopes p e,MixedFeatureTopology.coefficientReadout 1 (fixedHeadCoefficients p (e 3)),
    MixedFeatureTopology.coefficientReadout 1 (fixedHeadCoefficients p (e 4)))

/-- The complete fixed-feature-space head identity is forced by exactness of
the coefficient-identical physical lift. -/
lemma actualHeadData_reconstructs (p : Slice) (e : Equiv.Perm (Fin 5))
    (d : ResidualSystem (Fin 3)) (hd : d.Represents (time p))
    (he : ∀ y,(residualLift (time p) d (headSlopes p e)
      (originalHeadCoefficients p (e 3)) (originalHeadCoefficients p (e 4))).eval y=Maximum 4 y) :
    (HeadTopology.toHeads (actualHeadData p e)).Reconstructs
      (MixedFeatureTopology.coefficientReadout 1 (fixedRemainderCoefficients (time p) d) :
        InvariantState → ℝ) := by
  have hh := residualLift_heads_of_exact (time p) d (headSlopes p e)
    (originalHeadCoefficients p (e 3)) (originalHeadCoefficients p (e 4)) hd he
  intro x z
  have hx := hh (x.1/time p,x.2.1,x.2.2) z
  rw [← varying_fixedHeadCoefficients p (e 3),← varying_fixedHeadCoefficients p (e 4),
    coefficientHeads_varying_eval (time p) p.property.1] at hx
  have hq : time p*(x.1/time p)=x.1 := by
    have ht : time p ≠ 0 := ne_of_gt p.property.1
    field_simp [ht] <;> ring
  change (coefficientHeads 1 (headSlopes p e) (fixedHeadCoefficients p (e 3))
    (fixedHeadCoefficients p (e 4))).eval x z = z+
      readout 1 ((fixedRemainderCoefficients (time p) d) 0)
        ((fixedRemainderCoefficients (time p) d) 1)
        ((fixedRemainderCoefficients (time p) d) 2)
        ((fixedRemainderCoefficients (time p) d) 3) x
  rw [fixedRemainder_readout (time p) d p.property.1 x]
  simpa only [hq] using hx

lemma chartNetA_actualData (p : Slice) (e : Equiv.Perm (Fin 5)) (bits : Fin 3 → Bool)
    (b : ResidualChartBase) (ht : b.1.val=time p)
    (hh : (HeadTopology.toHeads (actualHeadData p e)).Reconstructs
      (MixedFeatureTopology.coefficientReadout 1 (fixedRemainderA bits b) : InvariantState → ℝ)) :
    chartNetA bits ⟨(b,actualHeadData p e),hh⟩ =
      residualLift (time p) (chartResidualA bits b) (headSlopes p e)
        (originalHeadCoefficients p (e 3)) (originalHeadCoefficients p (e 4)) := by
  simp only [chartNetA,actualHeadData,MixedFeatureTopology.recover_coefficientReadout
    (by norm_num : 0 < (1 : ℝ))]
  rw [ht,varying_fixedHeadCoefficients,varying_fixedHeadCoefficients]

lemma chartNetB_actualData (p : Slice) (e : Equiv.Perm (Fin 5)) (bits : Fin 3 → Bool)
    (b : ResidualChartBase) (ht : b.1.val=time p)
    (hh : (HeadTopology.toHeads (actualHeadData p e)).Reconstructs
      (MixedFeatureTopology.coefficientReadout 1 (fixedRemainderB bits b) : InvariantState → ℝ)) :
    chartNetB bits ⟨(b,actualHeadData p e),hh⟩ =
      residualLift (time p) (chartResidualB bits b) (headSlopes p e)
        (originalHeadCoefficients p (e 3)) (originalHeadCoefficients p (e 4)) := by
  simp only [chartNetB,actualHeadData,MixedFeatureTopology.recover_coefficientReadout
    (by norm_num : 0 < (1 : ℝ))]
  rw [ht,varying_fixedHeadCoefficients,varying_fixedHeadCoefficients]

lemma core_outputs_of_class (p : Slice) (l : Label) (hl : p ∈ physicalClass l) :
    (core p (rowOrder l)).out = ![1,1,-1] := by
  have ho := hl.1.1.1.1
  funext i
  fin_cases i
  · change output p (rowOrder l 0)=1
    exact ho 0
  · change output p (rowOrder l 1)=1
    exact ho 1
  · change output p (rowOrder l 2) = -1
    exact ho 2

/-- A given actual class in branch A is covered by the continuous physical
chart with exactly its original orientation bits. The equality matches all
network arrays after the genuine second-row permutation. -/
theorem physicalClass_chartA (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (hz : p.val.2.HasZeroBiases) (hb : branch l=false) :
    ∃ q : ResidualHeadChartA (orientations l),
      q.val.1.1.val=time p ∧ q.val.2=actualHeadData p (rowOrder l) ∧
      permuteHidden p.val.2 (Equiv.refl _) (rowOrder l)=chartNetA (orientations l) q := by
  have hd : 1 ≤ time p*parameter l p ∧
      (core p (rowOrder l)).HasADirections (time p) (parameter l p) := by
    simpa [directionClass,hb] using hl.1.2
  let b := extractedBaseA p (parameter l p) hd.1
  let d := chartResidualA (orientations l) b
  have hdcanonical : d=(canonicalResidualA (time p) (parameter l p)).flip (orientations l) := by
    dsimp only [d,chartResidualA,b]
    rw [chartK_extractedBaseA]
    rfl
  have hf : d.U=(core p (rowOrder l)).U ∧ d.V=(core p (rowOrder l)).V ∧
      d.W=(core p (rowOrder l)).W ∧ d.T=(core p (rowOrder l)).T ∧
      d.out=(core p (rowOrder l)).out := by
    rw [hdcanonical]
    exact canonicalResidualA_fields _ _ _ _ hd.2 hl.1.1.2 (core_outputs_of_class p l hl)
  have hnet : permuteHidden p.val.2 (Equiv.refl _) (rowOrder l)=
      residualLift (time p) d (headSlopes p (rowOrder l))
        (originalHeadCoefficients p (rowOrder l 3))
        (originalHeadCoefficients p (rowOrder l 4)) :=
    (permute_eq_actualLift p l hl hz).trans (residualLift_congr_fields _ _ _ _ _ _
      hf.1.symm hf.2.1.symm hf.2.2.1.symm hf.2.2.2.1.symm hf.2.2.2.2.symm)
  have hexact : ∀ y,(residualLift (time p) d (headSlopes p (rowOrder l))
      (originalHeadCoefficients p (rowOrder l 3))
      (originalHeadCoefficients p (rowOrder l 4))).eval y=Maximum 4 y := by
    intro y
    rw [← hnet,permuteHidden_eval]
    exact p.property.2.2.1 y
  have hh : (HeadTopology.toHeads (actualHeadData p (rowOrder l))).Reconstructs
      (MixedFeatureTopology.coefficientReadout 1 (fixedRemainderA (orientations l) b) :
        InvariantState → ℝ) :=
    actualHeadData_reconstructs p (rowOrder l) d (chartResidualA_represents _ b) hexact
  let q : ResidualHeadChartA (orientations l) := ⟨(b,actualHeadData p (rowOrder l)),hh⟩
  refine ⟨q,rfl,rfl,?_⟩
  exact hnet.trans (chartNetA_actualData p (rowOrder l) (orientations l) b rfl hh).symm

/-- The corresponding coefficient-identical coverage for the complete
branch-B physical class, including its closed endpoint. -/
theorem physicalClass_chartB (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (hz : p.val.2.HasZeroBiases) (hb : branch l=true) :
    ∃ q : ResidualHeadChartB (orientations l),
      q.val.1.1.val=time p ∧ q.val.2=actualHeadData p (rowOrder l) ∧
      permuteHidden p.val.2 (Equiv.refl _) (rowOrder l)=chartNetB (orientations l) q := by
  have hd : 1+time p ≤ time p*parameter l p ∧
      (core p (rowOrder l)).HasBDirections (time p) (parameter l p) := by
    simpa only [directionClass,Set.mem_setOf_eq,hb,if_true] using hl.1.2
  let b := extractedBaseB p (parameter l p) hd.1
  let d := chartResidualB (orientations l) b
  have hdcanonical : d=(canonicalResidualB (time p) (parameter l p)).flip (orientations l) := by
    dsimp only [d,chartResidualB,b]
    rw [chartR_extractedBaseB]
    rfl
  have hf : d.U=(core p (rowOrder l)).U ∧ d.V=(core p (rowOrder l)).V ∧
      d.W=(core p (rowOrder l)).W ∧ d.T=(core p (rowOrder l)).T ∧
      d.out=(core p (rowOrder l)).out := by
    rw [hdcanonical]
    exact canonicalResidualB_fields _ _ _ _ hd.2 hl.1.1.2 (core_outputs_of_class p l hl)
  have hnet : permuteHidden p.val.2 (Equiv.refl _) (rowOrder l)=
      residualLift (time p) d (headSlopes p (rowOrder l))
        (originalHeadCoefficients p (rowOrder l 3))
        (originalHeadCoefficients p (rowOrder l 4)) :=
    (permute_eq_actualLift p l hl hz).trans (residualLift_congr_fields _ _ _ _ _ _
      hf.1.symm hf.2.1.symm hf.2.2.1.symm hf.2.2.2.1.symm hf.2.2.2.2.symm)
  have hexact : ∀ y,(residualLift (time p) d (headSlopes p (rowOrder l))
      (originalHeadCoefficients p (rowOrder l 3))
      (originalHeadCoefficients p (rowOrder l 4))).eval y=Maximum 4 y := by
    intro y
    rw [← hnet,permuteHidden_eval]
    exact p.property.2.2.1 y
  have hh : (HeadTopology.toHeads (actualHeadData p (rowOrder l))).Reconstructs
      (MixedFeatureTopology.coefficientReadout 1 (fixedRemainderB (orientations l) b) :
        InvariantState → ℝ) :=
    actualHeadData_reconstructs p (rowOrder l) d (chartResidualB_represents _ b) hexact
  let q : ResidualHeadChartB (orientations l) := ⟨(b,actualHeadData p (rowOrder l)),hh⟩
  refine ⟨q,rfl,rfl,?_⟩
  exact hnet.trans (chartNetB_actualData p (rowOrder l) (orientations l) b rfl hh).symm

lemma actualHeadData_A (p : Slice) (e : Equiv.Perm (Fin 5)) (x : InvariantState) :
    (HeadTopology.toHeads (actualHeadData p e)).A x=
      intercept p (e 3) (x.1/time p,x.2.1,x.2.2) := by
  change readout 1 (coeff p (e 3) 0/time p) (coeff p (e 3) 1)
    (coeff p (e 3) 2) (coeff p (e 3) 3) x=
      readout (time p) (coeff p (e 3) 0) (coeff p (e 3) 1)
        (coeff p (e 3) 2) (coeff p (e 3) 3) (x.1/time p,x.2.1,x.2.2)
  exact (readout_fixed_coordinates (time p) _ _ _ _ p.property.1 x).symm

lemma actualHeadData_B (p : Slice) (e : Equiv.Perm (Fin 5)) (x : InvariantState) :
    (HeadTopology.toHeads (actualHeadData p e)).B x=
      intercept p (e 4) (x.1/time p,x.2.1,x.2.2) := by
  change readout 1 (coeff p (e 4) 0/time p) (coeff p (e 4) 1)
    (coeff p (e 4) 2) (coeff p (e 4) 3) x=
      readout (time p) (coeff p (e 4) 0) (coeff p (e 4) 1)
        (coeff p (e 4) 2) (coeff p (e 4) 3) (x.1/time p,x.2.1,x.2.2)
  exact (readout_fixed_coordinates (time p) _ _ _ _ p.property.1 x).symm

/-- The chart point retains the given physical label's head-kind test on the
whole real invariant domain, after the actual invertible coordinate change. -/
lemma physicalClass_headData_test (p : Slice) (l : Label) (hl : p ∈ physicalClass l) :
    if signed l then ∀ x : InvariantState,
      (HeadTopology.toHeads (actualHeadData p (rowOrder l))).A x+
        (HeadTopology.toHeads (actualHeadData p (rowOrder l))).B x=0
    else ∀ x : InvariantState,
      0 ≤ (HeadTopology.toHeads (actualHeadData p (rowOrder l))).A x ∧
        0 ≤ (HeadTopology.toHeads (actualHeadData p (rowOrder l))).B x := by
  have hh := hl.2
  cases hs : signed l
  · change ∀ x : InvariantState,
      0 ≤ (HeadTopology.toHeads (actualHeadData p (rowOrder l))).A x ∧
        0 ≤ (HeadTopology.toHeads (actualHeadData p (rowOrder l))).B x
    have hh : ∀ x : InvariantState,
        0 ≤ intercept p (rowOrder l 3) x ∧ 0 ≤ intercept p (rowOrder l 4) x := by
      simpa [headClass,hs] using hh
    intro x
    rw [actualHeadData_A,actualHeadData_B]
    exact hh _
  · change ∀ x : InvariantState,
      (HeadTopology.toHeads (actualHeadData p (rowOrder l))).A x+
        (HeadTopology.toHeads (actualHeadData p (rowOrder l))).B x=0
    have hh : ∀ x : InvariantState,
        intercept p (rowOrder l 3) x+intercept p (rowOrder l 4) x=0 := by
      simpa only [headClass,Set.mem_setOf_eq,hs,if_true] using hh
    intro x
    rw [actualHeadData_A,actualHeadData_B]
    exact hh _

/-- Every actual zero-bias normalized mixed physical network is, after a
genuine hidden-neuron permutation, literally a member of one of the two
continuous chart images. No label or residual form is an input hypothesis. -/
theorem zeroBias_chart_coverage (p : Slice) (hz : p.val.2.HasZeroBiases) :
    ∃ e : Equiv.Perm (Fin 5), ∃ bits : Fin 3 → Bool,
      (∃ q : ResidualHeadChartA bits, q.val.1.1.val=time p ∧
        q.val.2=actualHeadData p e ∧
        permuteHidden p.val.2 (Equiv.refl _) e=chartNetA bits q) ∨
      (∃ q : ResidualHeadChartB bits, q.val.1.1.val=time p ∧
        q.val.2=actualHeadData p e ∧
        permuteHidden p.val.2 (Equiv.refl _) e=chartNetB bits q) := by
  obtain ⟨l,hl⟩ := physicalClasses_exhaustive p
  refine ⟨rowOrder l,orientations l,?_⟩
  cases hb : branch l
  · exact Or.inl (physicalClass_chartA p l hl hz hb)
  · exact Or.inr (physicalClass_chartB p l hl hz hb)

#check @physicalClass_chartA
#check @physicalClass_chartB
#print axioms physicalClass_chartA
#print axioms physicalClass_chartB
#print axioms physicalClass_headData_test
#print axioms zeroBias_chart_coverage

end MaxCaterpillar.Fiber.Count65.ActualMixedLabels
