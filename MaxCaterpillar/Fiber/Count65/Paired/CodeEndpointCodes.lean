import MaxCaterpillar.Fiber.Count65.Paired.CodeOffsets
import Mathlib.Analysis.NormedSpace.Connected

/-! # Connected determinant-sign code spaces, without trigonometric coordinates -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open Set

abbrev Code := Fin 2 → Fin 2 → ℝ
abbrev PositiveCode := {U : Code // 0 < codeDet U}
abbrev CodeParameters := {u : Fin 2 → ℝ // u ≠ 0} × ℝ × {μ : ℝ // 0 < μ}

def reverseCode (U : Code) : Code :=
  ![![U 0 0,U 0 1],![-U 1 0,-U 1 1]]

lemma codeDet_reverseCode (U : Code) : codeDet (reverseCode U) = -codeDet U := by
  norm_num [codeDet,reverseCode]
  ring

lemma code_normsq_pos (u : Fin 2 → ℝ) (hu : u ≠ 0) : 0 < u 0*u 0+u 1*u 1 := by
  by_cases h0 : u 0=0
  · have h1 : u 1 ≠ 0 := by
      intro h1
      apply hu
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hs := mul_self_pos.mpr h1
    nlinarith only [hs,h0]
  · have hs := mul_self_pos.mpr h0
    have ht := mul_self_nonneg (u 1)
    nlinarith only [hs,ht]

/-- v=λu+μJu, with J(a,b)=(-b,a). -/
def codeOfParameters (p : CodeParameters) : Code :=
  ![![p.1.val 0,p.1.val 1],
    ![p.2.1*p.1.val 0-p.2.2.val*p.1.val 1,
      p.2.1*p.1.val 1+p.2.2.val*p.1.val 0]]

lemma codeOfParameters_det (p : CodeParameters) :
    codeDet (codeOfParameters p)=p.2.2.val*(p.1.val 0*p.1.val 0+p.1.val 1*p.1.val 1) := by
  norm_num [codeDet,codeOfParameters]
  ring

lemma codeOfParameters_positive (p : CodeParameters) : 0 < codeDet (codeOfParameters p) := by
  rw [codeOfParameters_det]
  exact mul_pos p.2.2.property (code_normsq_pos p.1.val p.1.property)

lemma continuous_codeOfParameters : Continuous codeOfParameters := by
  have hu (i : Fin 2) : Continuous (fun p : CodeParameters => p.1.val i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
  have hl : Continuous (fun p : CodeParameters => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hm : Continuous (fun p : CodeParameters => p.2.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · change Continuous (fun p : CodeParameters => p.1.val 0)
    exact hu 0
  · change Continuous (fun p : CodeParameters => p.1.val 1)
    exact hu 1
  · change Continuous (fun p : CodeParameters => p.2.1*p.1.val 0-p.2.2.val*p.1.val 1)
    exact (hl.mul (hu 0)).sub (hm.mul (hu 1))
  · change Continuous (fun p : CodeParameters => p.2.1*p.1.val 1+p.2.2.val*p.1.val 0)
    exact (hl.mul (hu 1)).add (hm.mul (hu 0))

lemma codeOfParameters_range : Set.range codeOfParameters={U : Code | 0 < codeDet U} := by
  ext U
  constructor
  · rintro ⟨p,rfl⟩
    exact codeOfParameters_positive p
  · intro hU
    change 0 < codeDet U at hU
    let u : Fin 2 → ℝ := ![U 0 0,U 0 1]
    have hu : u ≠ 0 := by
      intro hz
      have h0 := congrFun hz 0
      have h1 := congrFun hz 1
      change U 0 0=0 at h0
      change U 0 1=0 at h1
      have he : codeDet U=0 := by rw [codeDet,h0,h1]; ring
      exact hU.ne' he
    have hn : 0 < U 0 0*U 0 0+U 0 1*U 0 1 := code_normsq_pos u hu
    let ell := (U 0 0*U 1 0+U 0 1*U 1 1)/(U 0 0*U 0 0+U 0 1*U 0 1)
    let coeffMu := codeDet U/(U 0 0*U 0 0+U 0 1*U 0 1)
    let p : CodeParameters := (⟨u,hu⟩,ell,⟨coeffMu,div_pos hU hn⟩)
    refine ⟨p,?_⟩
    funext i j
    fin_cases i <;> fin_cases j
    · change U 0 0=U 0 0
      rfl
    · change U 0 1=U 0 1
      rfl
    · change ((U 0 0*U 1 0+U 0 1*U 1 1)/(U 0 0*U 0 0+U 0 1*U 0 1))*U 0 0-
        (codeDet U/(U 0 0*U 0 0+U 0 1*U 0 1))*U 0 1=U 1 0
      field_simp [hn.ne']
      unfold codeDet
      ring
    · change ((U 0 0*U 1 0+U 0 1*U 1 1)/(U 0 0*U 0 0+U 0 1*U 0 1))*U 0 1+
        (codeDet U/(U 0 0*U 0 0+U 0 1*U 0 1))*U 0 0=U 1 1
      field_simp [hn.ne']
      unfold codeDet
      ring

lemma codeParameters_pathConnected : PathConnectedSpace CodeParameters := by
  have hd : 1 < Module.rank ℝ (Fin 2 → ℝ) := by
    rw [rank_fin_fun]
    norm_num
  have hp := isPathConnected_compl_singleton_of_one_lt_rank hd (0 : Fin 2 → ℝ)
  have hpos : IsPathConnected (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).isPathConnected ⟨1,by norm_num⟩
  letI : PathConnectedSpace {u : Fin 2 → ℝ // u ≠ 0} := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    simpa only [Set.compl_singleton_eq] using hp
  letI : PathConnectedSpace {μ : ℝ // 0 < μ} :=
    isPathConnected_iff_pathConnectedSpace.mp hpos
  refine ⟨⟨(⟨![1,0],?_⟩,0,⟨1,by norm_num⟩)⟩,?_⟩
  · intro h
    have he := congrFun h 0
    norm_num at he
  · intro p q
    exact ⟨(PathConnectedSpace.somePath p.1 q.1).prod
      ((PathConnectedSpace.somePath p.2.1 q.2.1).prod
        (PathConnectedSpace.somePath p.2.2 q.2.2))⟩

/-- All positive-determinant anchor codes are joined, in their ordinary
four-coefficient topology; no angle choice or matrix logarithm is used. -/
theorem isPathConnected_positiveCode : IsPathConnected {U : Code | 0 < codeDet U} := by
  letI := codeParameters_pathConnected
  have h := isPathConnected_univ.image continuous_codeOfParameters
  simpa only [Set.image_univ,codeOfParameters_range] using h

theorem positiveCode_pathConnected : PathConnectedSpace PositiveCode :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_positiveCode

#print axioms isPathConnected_positiveCode
end MaxCaterpillar.Fiber.Count65.Paired
