import MaxCaterpillar.Fiber.Count65.Mixed.CanonicalResiduals
import MaxCaterpillar.Fiber.Count65.Mixed.ResidualNonzero
import Mathlib.Analysis.Convex.Topology

/-! # Continuous mixed residual charts in one fixed feature space

The domain is positive t times nonnegative slack. The coordinate substitution
q=q'/t identifies every moving feature space with the actual space at t=1.
The coefficient maps are those of the genuine oriented residual witnesses.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Mixed65
open BigOperators MaxCaterpillar.Frontier

abbrev ResidualChartBase := {t : ℝ // 0 < t} × {s : ℝ // 0 ≤ s}

theorem residualChartBase_pathConnected : PathConnectedSpace ResidualChartBase := by
  have hpos : IsPathConnected (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).isPathConnected ⟨1,by norm_num⟩
  have hnonneg : IsPathConnected (Set.Ici (0 : ℝ)) :=
    (convex_Ici (0 : ℝ)).isPathConnected ⟨0,by norm_num⟩
  letI : PathConnectedSpace {t : ℝ // 0 < t} :=
    isPathConnected_iff_pathConnectedSpace.mp hpos
  letI : PathConnectedSpace {s : ℝ // 0 ≤ s} :=
    isPathConnected_iff_pathConnectedSpace.mp hnonneg
  refine ⟨⟨(⟨1,by norm_num⟩,⟨0,by norm_num⟩)⟩,?_⟩
  intro x y
  exact ⟨(PathConnectedSpace.somePath x.1 y.1).prod
    (PathConnectedSpace.somePath x.2 y.2)⟩

noncomputable def chartK (p : ResidualChartBase) : ℝ := (1+p.2.val)/p.1.val
noncomputable def chartR (p : ResidualChartBase) : ℝ := (1+p.1.val+p.2.val)/p.1.val

lemma chartK_bound (p : ResidualChartBase) : 1 ≤ p.1.val*chartK p := by
  dsimp only [chartK]
  have he : p.1.val*((1+p.2.val)/p.1.val) = 1+p.2.val := by
    field_simp [p.1.property.ne']; ring
  rw [he]
  linarith only [p.2.property]

lemma chartR_bound (p : ResidualChartBase) : 1+p.1.val ≤ p.1.val*chartR p := by
  dsimp only [chartR]
  have he : p.1.val*((1+p.1.val+p.2.val)/p.1.val) = 1+p.1.val+p.2.val := by
    field_simp [p.1.property.ne']; ring
  rw [he]
  linarith only [p.2.property]

noncomputable def chartResidualA (bits : Fin 3 → Bool) (p : ResidualChartBase) :
    ResidualSystem (Fin 3) := (canonicalResidualA p.1.val (chartK p)).flip bits
noncomputable def chartResidualB (bits : Fin 3 → Bool) (p : ResidualChartBase) :
    ResidualSystem (Fin 3) := (canonicalResidualB p.1.val (chartR p)).flip bits

lemma chartResidualA_represents (bits : Fin 3 → Bool) (p : ResidualChartBase) :
    (chartResidualA bits p).Represents p.1.val :=
  (canonicalResidualA p.1.val (chartK p)).flip_represents bits p.1.val
    (canonicalResidualA_represents _ _ p.1.property (chartK_bound p))

lemma chartResidualB_represents (bits : Fin 3 → Bool) (p : ResidualChartBase) :
    (chartResidualB bits p).Represents p.1.val :=
  (canonicalResidualB p.1.val (chartR p)).flip_represents bits p.1.val
    (canonicalResidualB_represents _ _ p.1.property (chartR_bound p))

/-- This identity uses actual invariant inputs and the real four features. -/
lemma readout_fixed_coordinates (t A B C D : ℝ) (ht : 0 < t) (x : InvariantState) :
    readout t A B C D (x.1/t,x.2.1,x.2.2) = readout 1 (A/t) B C D x := by
  have hq : relu (x.1/t) = relu x.1/t := by
    rw [div_eq_mul_inv,mul_comm x.1 (t⁻¹),relu_mul_pos (inv_pos.mpr ht)]
    ring
  have htq : t*(x.1/t) = x.1 := by field_simp; ring
  simp only [readout,form,hq,htq,one_mul]
  ring

noncomputable def fixedRemainderCoefficients (t : ℝ) (d : ResidualSystem (Fin 3)) :
    Fin 4 → ℝ := ![d.lU/t,d.lV,d.lW,d.lT]

noncomputable def fixedRemainderA (bits : Fin 3 → Bool) (p : ResidualChartBase) :
    Fin 4 → ℝ := fixedRemainderCoefficients p.1.val (chartResidualA bits p)
noncomputable def fixedRemainderB (bits : Fin 3 → Bool) (p : ResidualChartBase) :
    Fin 4 → ℝ := fixedRemainderCoefficients p.1.val (chartResidualB bits p)

lemma continuous_chartK : Continuous chartK :=
  (continuous_const.add (continuous_subtype_val.comp continuous_snd)).div
    (continuous_subtype_val.comp continuous_fst) (fun p => p.1.property.ne')
lemma continuous_chartR : Continuous chartR :=
  ((continuous_const.add (continuous_subtype_val.comp continuous_fst)).add
    (continuous_subtype_val.comp continuous_snd)).div
    (continuous_subtype_val.comp continuous_fst) (fun p => p.1.property.ne')

lemma continuous_fixedRemainderA (bits : Fin 3 → Bool) : Continuous (fixedRemainderA bits) := by
  have ht : Continuous (fun p : ResidualChartBase => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hk := continuous_chartK
  apply continuous_pi
  intro i
  fin_cases i <;>
    norm_num [fixedRemainderA,fixedRemainderCoefficients,chartResidualA,
      ResidualSystem.flip,canonicalResidualA,Fin.sum_univ_succ]
  all_goals split_ifs <;> first
    | exact Continuous.div (by continuity) ht (fun p => p.1.property.ne')
    | continuity

lemma continuous_fixedRemainderB (bits : Fin 3 → Bool) : Continuous (fixedRemainderB bits) := by
  have ht : Continuous (fun p : ResidualChartBase => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hr := continuous_chartR
  apply continuous_pi
  intro i
  fin_cases i <;>
    norm_num [fixedRemainderB,fixedRemainderCoefficients,chartResidualB,
      ResidualSystem.flip,canonicalResidualB,Fin.sum_univ_succ]
  all_goals split_ifs <;> first
    | exact Continuous.div (by continuity) ht (fun p => p.1.property.ne')
    | continuity

lemma fixedRemainder_readout (t : ℝ) (d : ResidualSystem (Fin 3)) (ht : 0 < t)
    (x : InvariantState) :
    readout 1 ((fixedRemainderCoefficients t d) 0) ((fixedRemainderCoefficients t d) 1)
      ((fixedRemainderCoefficients t d) 2) ((fixedRemainderCoefficients t d) 3) x =
      d.base t (x.1/t) x.2.1 x.2.2 := by
  exact (readout_fixed_coordinates t d.lU d.lV d.lW d.lT ht x).symm

lemma fixedRemainderA_nonzero (bits : Fin 3 → Bool) (p : ResidualChartBase) :
    ∃ x : InvariantState, readout 1 ((fixedRemainderA bits p) 0)
      ((fixedRemainderA bits p) 1) ((fixedRemainderA bits p) 2)
      ((fixedRemainderA bits p) 3) x ≠ 0 := by
  obtain ⟨x,hx⟩ := (chartResidualA bits p).exists_nonzero_base p.1.val p.1.property
    (chartResidualA_represents bits p) rfl
  refine ⟨(p.1.val*x.1,x.2.1,x.2.2),?_⟩
  dsimp only [fixedRemainderA]
  rw [fixedRemainder_readout p.1.val (chartResidualA bits p) p.1.property]
  change (chartResidualA bits p).base p.1.val ((p.1.val*x.1)/p.1.val) x.2.1 x.2.2 ≠ 0
  have he : (p.1.val*x.1)/p.1.val = x.1 := by
    field_simp [p.1.property.ne']; ring
  rw [he]
  exact hx

lemma fixedRemainderB_nonzero (bits : Fin 3 → Bool) (p : ResidualChartBase) :
    ∃ x : InvariantState, readout 1 ((fixedRemainderB bits p) 0)
      ((fixedRemainderB bits p) 1) ((fixedRemainderB bits p) 2)
      ((fixedRemainderB bits p) 3) x ≠ 0 := by
  obtain ⟨x,hx⟩ := (chartResidualB bits p).exists_nonzero_base p.1.val p.1.property
    (chartResidualB_represents bits p) rfl
  refine ⟨(p.1.val*x.1,x.2.1,x.2.2),?_⟩
  dsimp only [fixedRemainderB]
  rw [fixedRemainder_readout p.1.val (chartResidualB bits p) p.1.property]
  change (chartResidualB bits p).base p.1.val ((p.1.val*x.1)/p.1.val) x.2.1 x.2.2 ≠ 0
  have he : (p.1.val*x.1)/p.1.val = x.1 := by
    field_simp [p.1.property.ne']; ring
  rw [he]
  exact hx

end MaxCaterpillar.Fiber.Mixed65
