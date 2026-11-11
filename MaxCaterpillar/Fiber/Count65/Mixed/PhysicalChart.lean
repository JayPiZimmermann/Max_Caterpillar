import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Fiber.Count65.Mixed.ChartComponents
import MaxCaterpillar.Fiber.Count65.Mixed.PhysicalAdapter
import MaxCaterpillar.Fiber.Count65.Mixed.FeatureTopology
import MaxCaterpillar.Fiber.Count65.HeadTopology

/-! # Actual network maps from mixed residual and head parameters

The rows are the left positive core, right positive core, negative core,
positive translation head and negative translation head. All biases are zero.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Mixed65
open BigOperators MaxCaterpillar.Frontier
open MaxCaterpillar.Fiber.Count65

@[simp] private lemma vecFour_three (a b c d : ℝ) : ![a,b,c,d] (3 : Fin 4) = d := rfl

noncomputable def residualLift (t : ℝ) (d : ResidualSystem (Fin 3))
    (s A B : Fin 4 → ℝ) : Network 4 6 5 where
  W₁ := firstRows t
  b₁ := 0
  W₂ := ![![d.U 0,d.V 0,d.W 0,d.T 0,0,0],
    ![d.U 1,d.V 1,d.W 1,d.T 1,0,0],
    ![d.U 2,d.V 2,d.W 2,d.T 2,0,0],
    ![A 0,A 1,A 2,A 3,s 0,s 1],
    ![B 0,B 1,B 2,B 3,s 2,s 3]]
  b₂ := 0
  w₃ := ![d.out 0,d.out 1,d.out 2,1,-1]
  b₃ := 0

noncomputable def coefficientHeads (t : ℝ) (s A B : Fin 4 → ℝ) : Heads InvariantState :=
  ⟨s 0,s 1,s 2,s 3,readout t (A 0) (A 1) (A 2) (A 3),
    readout t (B 0) (B 1) (B 2) (B 3)⟩

lemma residualLift_hasZeroBiases (t : ℝ) (d : ResidualSystem (Fin 3))
    (s A B : Fin 4 → ℝ) : (residualLift t d s A B).HasZeroBiases := ⟨rfl,rfl,rfl⟩

lemma residualLift_eval (t : ℝ) (d : ResidualSystem (Fin 3)) (s A B : Fin 4 → ℝ)
    (x : Point 4) :
    (residualLift t d s A B).eval x =
      (coefficientHeads t s A B).eval (x 0-x 1,x 1-x 2,x 3-x 2) (x 2) +
        ∑ i : Fin 3, d.out i*relu (d.gate t i (x 0-x 1) (x 1-x 2) (x 3-x 2)) := by
  simp only [Network.eval,residualLift,Pi.zero_apply,add_zero]
  simp_rw [firstRows_eval]
  norm_num [Fin.sum_univ_succ,firstValues,coefficientHeads,Heads.eval,readout,
    form,ResidualSystem.gate]
  ring

/-- A genuine all-input physical network, with no restrictions on its two
head reconstruction families beyond exact reconstruction itself. -/
theorem residualLift_exact (t : ℝ) (d : ResidualSystem (Fin 3)) (s A B : Fin 4 → ℝ)
    (hd : d.Represents t)
    (hh : (coefficientHeads t s A B).Reconstructs
      (fun x => d.base t x.1 x.2.1 x.2.2)) :
    ∀ x, (residualLift t d s A B).eval x = Maximum 4 x := by
  intro x
  rw [residualLift_eval,hh]
  have hr := hd (x 0-x 1) (x 1-x 2) (x 3-x 2)
  let q : InvariantState := (x 0-x 1,x 1-x 2,x 3-x 2)
  have hinv : translatedInput q (x 2) = x := by
    funext i
    fin_cases i <;> norm_num [translatedInput,q] <;> first | rfl | ring
  have hm := maximum_translatedInput q (x 2)
  rw [hinv] at hm
  change _ = x 2+max (max ((x 0-x 1)+(x 1-x 2)) (x 1-x 2)) (relu (x 3-x 2)) at hm
  change x 2+d.base t (x 0-x 1) (x 1-x 2) (x 3-x 2) + _ = _
  linarith only [hr,hm]

theorem continuous_residualLift {X : Type*} [TopologicalSpace X]
    (v : X → ℝ) (d : X → ResidualSystem (Fin 3)) (s A B : X → Fin 4 → ℝ)
    (hv : Continuous v) (hU : Continuous (fun x => (d x).U))
    (hV : Continuous (fun x => (d x).V)) (hW : Continuous (fun x => (d x).W))
    (hT : Continuous (fun x => (d x).T)) (ho : Continuous (fun x => (d x).out))
    (hs : Continuous s) (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => residualLift (v x) (d x) (s x) (A x) (B x)) := by
  apply (continuous_network_iff _).mpr
  refine ⟨?_,continuous_const,?_,continuous_const,?_,continuous_const⟩
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [residualLift,firstRows] <;> continuity
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [residualLift] <;> first
      | exact (continuous_apply _).comp hU
      | exact (continuous_apply _).comp hV
      | exact (continuous_apply _).comp hW
      | exact (continuous_apply _).comp hT
      | exact (continuous_apply _).comp hs
      | exact (continuous_apply _).comp hA
      | exact (continuous_apply _).comp hB
      | exact continuous_const
  · apply continuous_pi
    intro i
    fin_cases i <;> norm_num [residualLift] <;> first
      | exact (continuous_apply _).comp ho
      | exact continuous_const

/-- Convert coefficients in the fixed t=1 feature space to actual physical
coefficients in the mixed dictionary at t. -/
noncomputable def varyingCoefficients (t : ℝ) (A : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![t*A 0,A 1,A 2,A 3]

lemma varyingCoefficients_readout (t : ℝ) (ht : 0<t) (A : Fin 4 → ℝ) (x : InvariantState) :
    readout t ((varyingCoefficients t A) 0) ((varyingCoefficients t A) 1)
      ((varyingCoefficients t A) 2) ((varyingCoefficients t A) 3) x =
      readout 1 (A 0) (A 1) (A 2) (A 3) (t*x.1,x.2.1,x.2.2) := by
  have h := readout_fixed_coordinates t (t*A 0) (A 1) (A 2) (A 3) ht
    (t*x.1,x.2.1,x.2.2)
  have hq : t*x.1/t=x.1 := by field_simp [ht.ne']; ring
  have hA : t*A 0/t=A 0 := by field_simp [ht.ne']; ring
  simpa only [hq,hA] using h

lemma coefficientHeads_varying_eval (t : ℝ) (ht : 0<t) (s A B : Fin 4 → ℝ)
    (x : InvariantState) (z : ℝ) :
    (coefficientHeads t s (varyingCoefficients t A) (varyingCoefficients t B)).eval x z =
      (coefficientHeads 1 s A B).eval (t*x.1,x.2.1,x.2.2) z := by
  simp only [coefficientHeads,Heads.eval,varyingCoefficients_readout t ht]

lemma coefficientHeads_recover (h : HeadTopology.Data (featureSpace 1)) :
    coefficientHeads 1 h.1 (MixedFeatureTopology.recoverReadout 1 h.2.1)
      (MixedFeatureTopology.recoverReadout 1 h.2.2) = HeadTopology.toHeads h := by
  have hA := congrArg Subtype.val
    (MixedFeatureTopology.coefficientReadout_recover (by norm_num : 0 < (1 : ℝ)) h.2.1)
  have hB := congrArg Subtype.val
    (MixedFeatureTopology.coefficientReadout_recover (by norm_num : 0 < (1 : ℝ)) h.2.2)
  change readout 1 _ _ _ _ = (h.2.1 : InvariantState → ℝ) at hA
  change readout 1 _ _ _ _ = (h.2.2 : InvariantState → ℝ) at hB
  unfold coefficientHeads HeadTopology.toHeads
  rw [hA,hB]

noncomputable def chartNetA (bits : Fin 3 → Bool) (p : ResidualHeadChartA bits) :
    Network 4 6 5 :=
  let A := MixedFeatureTopology.recoverReadout 1 p.val.2.2.1
  let B := MixedFeatureTopology.recoverReadout 1 p.val.2.2.2
  residualLift p.val.1.1.val (chartResidualA bits p.val.1) p.val.2.1
    (varyingCoefficients p.val.1.1.val A) (varyingCoefficients p.val.1.1.val B)

noncomputable def chartNetB (bits : Fin 3 → Bool) (p : ResidualHeadChartB bits) :
    Network 4 6 5 :=
  let A := MixedFeatureTopology.recoverReadout 1 p.val.2.2.1
  let B := MixedFeatureTopology.recoverReadout 1 p.val.2.2.2
  residualLift p.val.1.1.val (chartResidualB bits p.val.1) p.val.2.1
    (varyingCoefficients p.val.1.1.val A) (varyingCoefficients p.val.1.1.val B)

lemma chartNetA_exact (bits : Fin 3 → Bool) (p : ResidualHeadChartA bits) :
    ∀ x, (chartNetA bits p).eval x = Maximum 4 x := by
  apply residualLift_exact _ _ _ _ _ (chartResidualA_represents bits p.val.1)
  intro x z
  rw [coefficientHeads_varying_eval _ p.val.1.1.property,coefficientHeads_recover]
  have hh := p.property (p.val.1.1.val*x.1,x.2.1,x.2.2) z
  dsimp only [MixedFeatureTopology.coefficientReadout,fixedRemainderA] at hh
  rw [fixedRemainder_readout _ _ p.val.1.1.property] at hh
  have hq : p.val.1.1.val*x.1/p.val.1.1.val=x.1 := by
    field_simp [p.val.1.1.property.ne']; ring
  simpa only [hq] using hh

lemma chartNetB_exact (bits : Fin 3 → Bool) (p : ResidualHeadChartB bits) :
    ∀ x, (chartNetB bits p).eval x = Maximum 4 x := by
  apply residualLift_exact _ _ _ _ _ (chartResidualB_represents bits p.val.1)
  intro x z
  rw [coefficientHeads_varying_eval _ p.val.1.1.property,coefficientHeads_recover]
  have hh := p.property (p.val.1.1.val*x.1,x.2.1,x.2.2) z
  dsimp only [MixedFeatureTopology.coefficientReadout,fixedRemainderB] at hh
  rw [fixedRemainder_readout _ _ p.val.1.1.property] at hh
  have hq : p.val.1.1.val*x.1/p.val.1.1.val=x.1 := by
    field_simp [p.val.1.1.property.ne']; ring
  simpa only [hq] using hh

lemma continuous_varyingCoefficients {X : Type*} [TopologicalSpace X]
    (v : X → ℝ) (A : X → Fin 4 → ℝ) (hv : Continuous v) (hA : Continuous A) :
    Continuous (fun x => varyingCoefficients (v x) (A x)) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun x => v x*A x 0)
    exact hv.mul ((continuous_apply 0).comp hA)
  · change Continuous (fun x => A x 1)
    exact (continuous_apply 1).comp hA
  · change Continuous (fun x => A x 2)
    exact (continuous_apply 2).comp hA
  · change Continuous (fun x => A x 3)
    exact (continuous_apply 3).comp hA

lemma continuous_chartResidualA_fields (bits : Fin 3 → Bool) :
    Continuous (fun p => (chartResidualA bits p).U) ∧
    Continuous (fun p => (chartResidualA bits p).V) ∧
    Continuous (fun p => (chartResidualA bits p).W) ∧
    Continuous (fun p => (chartResidualA bits p).T) ∧
    Continuous (fun p => (chartResidualA bits p).out) := by
  have ht : Continuous (fun p : ResidualChartBase => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hk := continuous_chartK
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals apply continuous_pi
  all_goals intro i
  all_goals fin_cases i <;>
    norm_num [chartResidualA,ResidualSystem.flip,canonicalResidualA] <;>
    first | exact continuous_const | (split_ifs <;> continuity)

lemma continuous_chartResidualB_fields (bits : Fin 3 → Bool) :
    Continuous (fun p => (chartResidualB bits p).U) ∧
    Continuous (fun p => (chartResidualB bits p).V) ∧
    Continuous (fun p => (chartResidualB bits p).W) ∧
    Continuous (fun p => (chartResidualB bits p).T) ∧
    Continuous (fun p => (chartResidualB bits p).out) := by
  have ht : Continuous (fun p : ResidualChartBase => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hr := continuous_chartR
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals apply continuous_pi
  all_goals intro i
  all_goals fin_cases i <;>
    norm_num [chartResidualB,ResidualSystem.flip,canonicalResidualB] <;>
    first | exact continuous_const | (split_ifs <;> continuity)

noncomputable def physicalChartFamily (d : ResidualChartBase → ResidualSystem (Fin 3))
    (p : ResidualChartBase × HeadTopology.Data (featureSpace 1)) : Network 4 6 5 :=
  residualLift p.1.1.val (d p.1) p.2.1
    (varyingCoefficients p.1.1.val (MixedFeatureTopology.recoverReadout 1 p.2.2.1))
    (varyingCoefficients p.1.1.val (MixedFeatureTopology.recoverReadout 1 p.2.2.2))

lemma continuous_physicalChartFamily (d : ResidualChartBase → ResidualSystem (Fin 3))
    (hU : Continuous (fun p => (d p).U)) (hV : Continuous (fun p => (d p).V))
    (hW : Continuous (fun p => (d p).W)) (hT : Continuous (fun p => (d p).T))
    (ho : Continuous (fun p => (d p).out)) : Continuous (physicalChartFamily d) := by
  have ht : Continuous (fun p : ResidualChartBase × HeadTopology.Data (featureSpace 1) =>
      p.1.1.val) := continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  apply continuous_residualLift _ _ _ _ _ ht (hU.comp continuous_fst)
    (hV.comp continuous_fst) (hW.comp continuous_fst) (hT.comp continuous_fst)
    (ho.comp continuous_fst) (continuous_fst.comp continuous_snd)
  · apply continuous_varyingCoefficients _ _ ht
    exact (MixedFeatureTopology.continuous_recoverReadout 1).comp
      (continuous_fst.comp (continuous_snd.comp continuous_snd))
  · apply continuous_varyingCoefficients _ _ ht
    exact (MixedFeatureTopology.continuous_recoverReadout 1).comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))

lemma continuous_chartNetA (bits : Fin 3 → Bool) : Continuous (chartNetA bits) := by
  obtain ⟨hU,hV,hW,hT,ho⟩ := continuous_chartResidualA_fields bits
  exact (continuous_physicalChartFamily (chartResidualA bits) hU hV hW hT ho).comp
    continuous_subtype_val

lemma continuous_chartNetB (bits : Fin 3 → Bool) : Continuous (chartNetB bits) := by
  obtain ⟨hU,hV,hW,hT,ho⟩ := continuous_chartResidualB_fields bits
  exact (continuous_physicalChartFamily (chartResidualB bits) hU hV hW hT ho).comp
    continuous_subtype_val

end MaxCaterpillar.Fiber.Mixed65
