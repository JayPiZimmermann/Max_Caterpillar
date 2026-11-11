import MaxCaterpillar.Fiber.Count65.SectorComponents
import MaxCaterpillar.Fiber.Count65.Mixed.ActualChartCoverage

/-! # Exact finite classes of the actual mixed physical chart images -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65.ActualMixedLabels
open Set Function Mixed65 MixedSectorComponents MaxCaterpillar.Frontier

lemma eps_square (bits : Fin 3 → Bool) (i : Fin 3) : eps bits i*eps bits i=1 := by
  unfold eps
  split_ifs <;> norm_num

/-- On the exact nonzero reconstruction fiber the two finite head labels
are equivalent to their closed all-real intercept tests. -/
lemma headKind_iff_test (D : HeadTopology.Data (featureSpace 1)) (L : featureSpace 1)
    (hr : (HeadTopology.toHeads D).Reconstructs (L : InvariantState → ℝ))
    (hnz : ∃ x,(L : InvariantState → ℝ) x ≠ 0) (kind : Bool) :
    (if kind then (HeadTopology.toHeads D).IsSigned (L : InvariantState → ℝ)
      else ¬ (HeadTopology.toHeads D).IsSigned (L : InvariantState → ℝ)) ↔
    (if kind then ∀ x : InvariantState,
      (HeadTopology.toHeads D).A x+(HeadTopology.toHeads D).B x=0
    else ∀ x : InvariantState,
      0 ≤ (HeadTopology.toHeads D).A x ∧ 0 ≤ (HeadTopology.toHeads D).B x) := by
  let h := HeadTopology.toHeads D
  cases kind
  · constructor
    · intro hn
      have hh := (Heads.reconstructs_iff_signed_or_splitHybrid (featureSpace 1)
        (featureSpace_clipping_rigid (by norm_num : 0 < (1 : ℝ))) h
        (L : InvariantState → ℝ) D.2.1.property D.2.2.property L.property).mp hr
      have hh := (hh.resolve_left hn).intercepts_nonneg
      exact fun x => ⟨hh.1 x,hh.2 x⟩
    · intro ht hs
      obtain ⟨x,hx⟩ := hnz
      have hp : 0 ≤ (L : InvariantState → ℝ) x := by
        simpa only [hs.1] using (ht x).1
      have hn : 0 ≤ -(L : InvariantState → ℝ) x := by
        simpa only [hs.2.1] using (ht x).2
      exact hx (by linarith only [hp,hn])
  · constructor
    · intro hs x
      rw [hs.1,hs.2.1]
      exact add_neg_self _
    · intro ht
      apply (HeadTopology.signed_iff_intercepts (featureSpace 1)
        (featureSpace_clipping_rigid (by norm_num : 0 < (1 : ℝ))) h
        (L : InvariantState → ℝ) D.2.1.property D.2.2.property L.property hr hnz).mpr
      have ha : h.A=(L : InvariantState → ℝ) := by
        funext x
        have hb : h.B x = -h.A x := by linarith only [ht x]
        have hv := hr x 0
        norm_num [Heads.eval,relu] at hv
        rw [hb] at hv
        have hpos := relu_sub_relu_neg (h.A x)
        unfold relu at hpos
        linarith only [hv,hpos]
      refine ⟨ha,?_⟩
      funext x
      have hh := ht x
      change h.A x+h.B x=0 at hh
      rw [ha] at hh
      linarith only [hh]

lemma headSectorA_test (bits : Fin 3 → Bool) (kind : Bool)
    (q : ResidualHeadChartA bits) (hq : q ∈ headSectorA bits kind) :
    if kind then ∀ x : InvariantState,
      (HeadTopology.toHeads q.val.2).A x+(HeadTopology.toHeads q.val.2).B x=0
    else ∀ x : InvariantState,
      0 ≤ (HeadTopology.toHeads q.val.2).A x ∧ 0 ≤ (HeadTopology.toHeads q.val.2).B x := by
  apply (headKind_iff_test q.val.2 _ q.property (fixedRemainderA_nonzero bits q.val.1) kind).mp
  cases kind <;> simpa [headSectorA,HeadTopology.bundleSignedSector] using hq

lemma headSectorB_test (bits : Fin 3 → Bool) (kind : Bool)
    (q : ResidualHeadChartB bits) (hq : q ∈ headSectorB bits kind) :
    if kind then ∀ x : InvariantState,
      (HeadTopology.toHeads q.val.2).A x+(HeadTopology.toHeads q.val.2).B x=0
    else ∀ x : InvariantState,
      0 ≤ (HeadTopology.toHeads q.val.2).A x ∧ 0 ≤ (HeadTopology.toHeads q.val.2).B x := by
  apply (headKind_iff_test q.val.2 _ q.property (fixedRemainderB_nonzero bits q.val.1) kind).mp
  cases kind <;> simpa [headSectorB,HeadTopology.bundleSignedSector] using hq

lemma chartA_intercept_positive (bits : Fin 3 → Bool) (q : ResidualHeadChartA bits)
    (x : InvariantState) : intercept (chartA bits q) 3 x=
      (HeadTopology.toHeads q.val.2).A (q.val.1.1.val*x.1,x.2.1,x.2.2) := by
  change readout q.val.1.1.val
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.1)) 0)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.1)) 1)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.1)) 2)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.1)) 3) x=_
  rw [varyingCoefficients_readout _ q.val.1.1.property]
  exact congrFun (congrArg Subtype.val (MixedFeatureTopology.coefficientReadout_recover
    (by norm_num : 0 < (1 : ℝ)) q.val.2.2.1)) _

lemma chartA_intercept_negative (bits : Fin 3 → Bool) (q : ResidualHeadChartA bits)
    (x : InvariantState) : intercept (chartA bits q) 4 x=
      (HeadTopology.toHeads q.val.2).B (q.val.1.1.val*x.1,x.2.1,x.2.2) := by
  change readout q.val.1.1.val
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.2)) 0)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.2)) 1)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.2)) 2)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.2)) 3) x=_
  rw [varyingCoefficients_readout _ q.val.1.1.property]
  exact congrFun (congrArg Subtype.val (MixedFeatureTopology.coefficientReadout_recover
    (by norm_num : 0 < (1 : ℝ)) q.val.2.2.2)) _

lemma chartB_intercept_positive (bits : Fin 3 → Bool) (q : ResidualHeadChartB bits)
    (x : InvariantState) : intercept (chartB bits q) 3 x=
      (HeadTopology.toHeads q.val.2).A (q.val.1.1.val*x.1,x.2.1,x.2.2) := by
  change readout q.val.1.1.val
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.1)) 0)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.1)) 1)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.1)) 2)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.1)) 3) x=_
  rw [varyingCoefficients_readout _ q.val.1.1.property]
  exact congrFun (congrArg Subtype.val (MixedFeatureTopology.coefficientReadout_recover
    (by norm_num : 0 < (1 : ℝ)) q.val.2.2.1)) _

lemma chartB_intercept_negative (bits : Fin 3 → Bool) (q : ResidualHeadChartB bits)
    (x : InvariantState) : intercept (chartB bits q) 4 x=
      (HeadTopology.toHeads q.val.2).B (q.val.1.1.val*x.1,x.2.1,x.2.2) := by
  change readout q.val.1.1.val
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.2)) 0)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.2)) 1)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.2)) 2)
    ((varyingCoefficients q.val.1.1.val (MixedFeatureTopology.recoverReadout 1 q.val.2.2.2)) 3) x=_
  rw [varyingCoefficients_readout _ q.val.1.1.property]
  exact congrFun (congrArg Subtype.val (MixedFeatureTopology.coefficientReadout_recover
    (by norm_num : 0 < (1 : ℝ)) q.val.2.2.2)) _

lemma canonicalResidualA_directions (t k : ℝ) (bits : Fin 3 → Bool) :
    ((canonicalResidualA t k).flip bits).HasADirections t k := by
  unfold ResidualSystem.HasADirections
  norm_num [ResidualSystem.flip,canonicalResidualA]
  repeat' constructor
  all_goals split_ifs <;> ring

lemma canonicalResidualB_directions (t v : ℝ) (bits : Fin 3 → Bool) :
    ((canonicalResidualB t v).flip bits).HasBDirections t v := by
  unfold ResidualSystem.HasBDirections
  norm_num [ResidualSystem.flip,canonicalResidualB]
  repeat' constructor
  all_goals split_ifs <;> ring

lemma chartResidualA_orientations (bits : Fin 3 → Bool) (b : ResidualChartBase)
    (i : Fin 3) : (chartResidualA bits b).W i=eps bits i := by
  fin_cases i <;> rfl
lemma chartResidualB_orientations (bits : Fin 3 → Bool) (b : ResidualChartBase)
    (i : Fin 3) : (chartResidualB bits b).W i=eps bits i := by
  fin_cases i <;> rfl

lemma chartA_core_fields (bits : Fin 3 → Bool) (q : ResidualHeadChartA bits) :
    (core (chartA bits q) (Equiv.refl _)).U=(chartResidualA bits q.val.1).U ∧
    (core (chartA bits q) (Equiv.refl _)).V=(chartResidualA bits q.val.1).V ∧
    (core (chartA bits q) (Equiv.refl _)).W=(chartResidualA bits q.val.1).W ∧
    (core (chartA bits q) (Equiv.refl _)).T=(chartResidualA bits q.val.1).T ∧
    (core (chartA bits q) (Equiv.refl _)).out=(chartResidualA bits q.val.1).out := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals funext i
  all_goals fin_cases i <;> rfl

lemma chartB_core_fields (bits : Fin 3 → Bool) (q : ResidualHeadChartB bits) :
    (core (chartB bits q) (Equiv.refl _)).U=(chartResidualB bits q.val.1).U ∧
    (core (chartB bits q) (Equiv.refl _)).V=(chartResidualB bits q.val.1).V ∧
    (core (chartB bits q) (Equiv.refl _)).W=(chartResidualB bits q.val.1).W ∧
    (core (chartB bits q) (Equiv.refl _)).T=(chartResidualB bits q.val.1).T ∧
    (core (chartB bits q) (Equiv.refl _)).out=(chartResidualB bits q.val.1).out := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals funext i
  all_goals fin_cases i <;> rfl

lemma parameter_A_of_directions (p : Slice) (e : Equiv.Perm (Fin 5))
    (bits : Fin 3 → Bool) (kind : Bool) (k : ℝ)
    (hd : (core p e).HasADirections (time p) k)
    (hw : ∀ i,(core p e).W i=eps bits i) : parameter (e,false,bits,kind) p=k := by
  change eps bits 1*coeff p (e 1) 3=k
  have hh := hd.2.2.2.2.2.1
  change coeff p (e 1) 3=k*(core p e).W 1 at hh
  rw [hh,hw]
  calc
    eps bits 1*(k*eps bits 1)=k*(eps bits 1*eps bits 1) := by ring
    _ = k := by rw [eps_square]; ring

lemma parameter_B_of_directions (p : Slice) (e : Equiv.Perm (Fin 5))
    (bits : Fin 3 → Bool) (kind : Bool) (v : ℝ)
    (hd : (core p e).HasBDirections (time p) v)
    (hw : ∀ i,(core p e).W i=eps bits i) : parameter (e,true,bits,kind) p=v := by
  change eps bits 0*coeff p (e 0) 1=v
  have hh := hd.2.1
  change coeff p (e 0) 1=v*(core p e).W 0 at hh
  rw [hh,hw]
  calc
    eps bits 0*(v*eps bits 0)=v*(eps bits 0*eps bits 0) := by ring
    _ = v := by rw [eps_square]; ring

/-- Every point of the connected A/head-kind chart has its exact physical
class: identity row order, branch A, the same three orientations and head kind. -/
theorem chartA_mem_physicalClass (bits : Fin 3 → Bool) (kind : Bool)
    (q : ResidualHeadChartA bits) (hq : q ∈ headSectorA bits kind) :
    chartA bits q ∈ physicalClass (Equiv.refl (Fin 5),false,bits,kind) := by
  let p := chartA bits q
  have hf := chartA_core_fields bits q
  have hw : ∀ i,(core p (Equiv.refl _)).W i=eps bits i := by
    intro i
    rw [hf.2.2.1]
    exact chartResidualA_orientations bits q.val.1 i
  have hd : (core p (Equiv.refl _)).HasADirections (time p) (chartK q.val.1) := by
    have hh : (chartResidualA bits q.val.1).HasADirections (time p) (chartK q.val.1) :=
      canonicalResidualA_directions _ _ _
    unfold ResidualSystem.HasADirections at hh ⊢
    simpa only [hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1] using hh
  have ho : p ∈ outputClass (Equiv.refl (Fin 5),false,bits,kind) := by
    intro i
    fin_cases i <;> rfl
  have hs : p ∈ stationaryClass (Equiv.refl (Fin 5),false,bits,kind) := by
    intro i
    fin_cases i <;> exact ⟨rfl,rfl⟩
  have hdir : p ∈ directionClass (Equiv.refl (Fin 5),false,bits,kind) := by
    change 1 ≤ time p*parameter (Equiv.refl _,false,bits,kind) p ∧ _
    rw [parameter_A_of_directions p (Equiv.refl _) bits kind _ hd hw]
    exact ⟨chartK_bound q.val.1,hd⟩
  have ht := headSectorA_test bits kind q hq
  have hh : p ∈ headClass (Equiv.refl (Fin 5),false,bits,kind) := by
    cases kind
    · change ∀ x : InvariantState,0 ≤ intercept (chartA bits q) 3 x ∧
        0 ≤ intercept (chartA bits q) 4 x
      intro x
      rw [chartA_intercept_positive,chartA_intercept_negative]
      exact ht _
    · change ∀ x : InvariantState,intercept (chartA bits q) 3 x+
        intercept (chartA bits q) 4 x=0
      intro x
      rw [chartA_intercept_positive,chartA_intercept_negative]
      exact ht _
  exact ⟨⟨⟨⟨ho,hs⟩,hw⟩,hdir⟩,hh⟩

/-- The complete B chart, including its closed boundary, has exactly the
corresponding original-coefficient physical class. -/
theorem chartB_mem_physicalClass (bits : Fin 3 → Bool) (kind : Bool)
    (q : ResidualHeadChartB bits) (hq : q ∈ headSectorB bits kind) :
    chartB bits q ∈ physicalClass (Equiv.refl (Fin 5),true,bits,kind) := by
  let p := chartB bits q
  have hf := chartB_core_fields bits q
  have hw : ∀ i,(core p (Equiv.refl _)).W i=eps bits i := by
    intro i
    rw [hf.2.2.1]
    exact chartResidualB_orientations bits q.val.1 i
  have hd : (core p (Equiv.refl _)).HasBDirections (time p) (chartR q.val.1) := by
    have hh : (chartResidualB bits q.val.1).HasBDirections (time p) (chartR q.val.1) :=
      canonicalResidualB_directions _ _ _
    unfold ResidualSystem.HasBDirections at hh ⊢
    simpa only [hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1] using hh
  have ho : p ∈ outputClass (Equiv.refl (Fin 5),true,bits,kind) := by
    intro i
    fin_cases i <;> rfl
  have hs : p ∈ stationaryClass (Equiv.refl (Fin 5),true,bits,kind) := by
    intro i
    fin_cases i <;> exact ⟨rfl,rfl⟩
  have hdir : p ∈ directionClass (Equiv.refl (Fin 5),true,bits,kind) := by
    change 1+time p ≤ time p*parameter (Equiv.refl _,true,bits,kind) p ∧ _
    rw [parameter_B_of_directions p (Equiv.refl _) bits kind _ hd hw]
    exact ⟨chartR_bound q.val.1,hd⟩
  have ht := headSectorB_test bits kind q hq
  have hh : p ∈ headClass (Equiv.refl (Fin 5),true,bits,kind) := by
    cases kind
    · change ∀ x : InvariantState,0 ≤ intercept (chartB bits q) 3 x ∧
        0 ≤ intercept (chartB bits q) 4 x
      intro x
      rw [chartB_intercept_positive,chartB_intercept_negative]
      exact ht _
    · change ∀ x : InvariantState,intercept (chartB bits q) 3 x+
        intercept (chartB bits q) 4 x=0
      intro x
      rw [chartB_intercept_positive,chartB_intercept_negative]
      exact ht _
  exact ⟨⟨⟨⟨ho,hs⟩,hw⟩,hdir⟩,hh⟩

lemma headSectorA_iff_test (bits : Fin 3 → Bool) (kind : Bool)
    (q : ResidualHeadChartA bits) : q ∈ headSectorA bits kind ↔
    (if kind then ∀ x : InvariantState,
      (HeadTopology.toHeads q.val.2).A x+(HeadTopology.toHeads q.val.2).B x=0
    else ∀ x : InvariantState,
      0 ≤ (HeadTopology.toHeads q.val.2).A x ∧ 0 ≤ (HeadTopology.toHeads q.val.2).B x) := by
  have hh := headKind_iff_test q.val.2 _ q.property (fixedRemainderA_nonzero bits q.val.1) kind
  cases kind <;> simpa [headSectorA,HeadTopology.bundleSignedSector] using hh

lemma headSectorB_iff_test (bits : Fin 3 → Bool) (kind : Bool)
    (q : ResidualHeadChartB bits) : q ∈ headSectorB bits kind ↔
    (if kind then ∀ x : InvariantState,
      (HeadTopology.toHeads q.val.2).A x+(HeadTopology.toHeads q.val.2).B x=0
    else ∀ x : InvariantState,
      0 ≤ (HeadTopology.toHeads q.val.2).A x ∧ 0 ≤ (HeadTopology.toHeads q.val.2).B x) := by
  have hh := headKind_iff_test q.val.2 _ q.property (fixedRemainderB_nonzero bits q.val.1) kind
  cases kind <;> simpa [headSectorB,HeadTopology.bundleSignedSector] using hh

/-- A recovered chart point lies in precisely the original physical head-kind
sector; this direction is needed for equality with the entire actual class. -/
lemma headSectorA_of_actualData (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (q : ResidualHeadChartA (orientations l))
    (hData : q.val.2=actualHeadData p (rowOrder l)) :
    q ∈ headSectorA (orientations l) (signed l) := by
  apply (headSectorA_iff_test _ _ q).mpr
  rw [hData]
  exact physicalClass_headData_test p l hl

lemma headSectorB_of_actualData (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (q : ResidualHeadChartB (orientations l))
    (hData : q.val.2=actualHeadData p (rowOrder l)) :
    q ∈ headSectorB (orientations l) (signed l) := by
  apply (headSectorB_iff_test _ _ q).mpr
  rw [hData]
  exact physicalClass_headData_test p l hl

theorem physicalClass_chartA_in_headSector (p : Slice) (l : Label)
    (hl : p ∈ physicalClass l) (hz : p.val.2.HasZeroBiases) (hb : branch l=false) :
    ∃ q : ResidualHeadChartA (orientations l),
      q ∈ headSectorA (orientations l) (signed l) ∧ q.val.1.1.val=time p ∧
      permuteHidden p.val.2 (Equiv.refl _) (rowOrder l)=chartNetA (orientations l) q := by
  obtain ⟨q,ht,hD,hnet⟩ := physicalClass_chartA p l hl hz hb
  exact ⟨q,headSectorA_of_actualData p l hl q hD,ht,hnet⟩

theorem physicalClass_chartB_in_headSector (p : Slice) (l : Label)
    (hl : p ∈ physicalClass l) (hz : p.val.2.HasZeroBiases) (hb : branch l=true) :
    ∃ q : ResidualHeadChartB (orientations l),
      q ∈ headSectorB (orientations l) (signed l) ∧ q.val.1.1.val=time p ∧
      permuteHidden p.val.2 (Equiv.refl _) (rowOrder l)=chartNetB (orientations l) q := by
  obtain ⟨q,ht,hD,hnet⟩ := physicalClass_chartB p l hl hz hb
  exact ⟨q,headSectorB_of_actualData p l hl q hD,ht,hnet⟩

lemma actualLabel_chartA (bits : Fin 3 → Bool) (kind : Bool)
    (q : ResidualHeadChartA bits) (hq : q ∈ headSectorA bits kind) :
    actualLabel (chartA bits q)=(Equiv.refl (Fin 5),false,bits,kind) :=
  (actualLabel_eq_iff _ _).mpr (chartA_mem_physicalClass bits kind q hq)
lemma actualLabel_chartB (bits : Fin 3 → Bool) (kind : Bool)
    (q : ResidualHeadChartB bits) (hq : q ∈ headSectorB bits kind) :
    actualLabel (chartB bits q)=(Equiv.refl (Fin 5),true,bits,kind) :=
  (actualLabel_eq_iff _ _).mpr (chartB_mem_physicalClass bits kind q hq)

lemma componentLabel_chartA (bits : Fin 3 → Bool) (kind : Bool)
    (q : ResidualHeadChartA bits) (hq : q ∈ headSectorA bits kind) :
    componentLabel (chartA bits q)=(false,bits,kind) := by
  unfold componentLabel
  rw [actualLabel_chartA bits kind q hq]
lemma componentLabel_chartB (bits : Fin 3 → Bool) (kind : Bool)
    (q : ResidualHeadChartB bits) (hq : q ∈ headSectorB bits kind) :
    componentLabel (chartB bits q)=(true,bits,kind) := by
  unfold componentLabel
  rw [actualLabel_chartB bits kind q hq]

#print axioms chartA_mem_physicalClass
#print axioms chartB_mem_physicalClass
#print axioms physicalClass_chartA_in_headSector
#print axioms physicalClass_chartB_in_headSector
#print axioms componentLabel_chartA
#print axioms componentLabel_chartB

end MaxCaterpillar.Fiber.Count65.ActualMixedLabels
