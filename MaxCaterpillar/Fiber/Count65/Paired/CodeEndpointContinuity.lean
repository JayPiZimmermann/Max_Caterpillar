import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointNetwork

/-! # Continuity of the actual invertible-code endpoint family -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired

variable {X : Type*} [TopologicalSpace X]

lemma continuous_codeDet_of (U : X → Fin 2 → Fin 2 → ℝ) (hU : Continuous U) :
    Continuous (fun x => codeDet (U x)) := by
  have hc (i j : Fin 2) : Continuous (fun x => U x i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hU)
  exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))

lemma continuous_inverseCode_of (U : X → Fin 2 → Fin 2 → ℝ) (hU : Continuous U)
    (hne : ∀ x,codeDet (U x) ≠ 0) : Continuous (fun x => inverseCode (U x)) := by
  have hc (i j : Fin 2) : Continuous (fun x => U x i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hU)
  have hd := continuous_codeDet_of U hU
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact (hc 1 1).div hd hne
  · exact (hc 0 1).neg.div hd hne
  · exact (hc 1 0).neg.div hd hne
  · exact (hc 0 0).div hd hne

lemma continuous_leftEndpointRow_of (U : X → Fin 2 → Fin 2 → ℝ) (hU : Continuous U)
    (hne : ∀ x,codeDet (U x) ≠ 0) : Continuous (fun x => leftEndpointRow (U x)) := by
  have hR := continuous_inverseCode_of U hU hne
  have hr (i j : Fin 2) : Continuous (fun x => inverseCode (U x) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hR)
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact hr 0 0
  · exact (hr 0 0).neg
  · exact hr 0 1
  · exact (hr 0 1).neg

lemma continuous_baselineRow_of (U : X → Fin 2 → Fin 2 → ℝ) (hU : Continuous U)
    (hne : ∀ x,codeDet (U x) ≠ 0) : Continuous (fun x => baselineRow (U x)) := by
  have hR := continuous_inverseCode_of U hU hne
  have hr (i j : Fin 2) : Continuous (fun x => inverseCode (U x) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hR)
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact hr 1 0
  · exact (hr 1 0).neg
  · exact hr 1 1
  · exact (hr 1 1).neg

lemma continuous_comparisonRow_of (U : X → Fin 2 → Fin 2 → ℝ) (hU : Continuous U)
    (hne : ∀ x,codeDet (U x) ≠ 0) : Continuous (fun x => comparisonRow (U x)) := by
  simpa only [comparisonRow_eq_sub] using
    (continuous_leftEndpointRow_of U hU hne).sub (continuous_baselineRow_of U hU hne)

/-- Continuity uses only invertibility; the original first and second physical
arrays both vary with the code, in the usual real parameter topology. -/
theorem continuous_pairedMinimalNet_of (U : X → Fin 2 → Fin 2 → ℝ) (hU : Continuous U)
    (hne : ∀ x,codeDet (U x) ≠ 0) : Continuous (fun x => pairedMinimalNet (U x)) := by
  have hc (i j : Fin 2) : Continuous (fun x => U x i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hU)
  apply (continuous_network_iff _).mpr
  refine ⟨?_,continuous_const,?_,continuous_const,continuous_const,continuous_const⟩
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [pairedMinimalNet,pairedRows] <;> first
      | exact continuous_const
      | exact hc _ _
      | exact (hc _ _).neg
  · apply continuous_pi
    intro k
    fin_cases k
    · exact continuous_baselineRow_of U hU hne
    · exact (continuous_baselineRow_of U hU hne).neg
    · exact continuous_comparisonRow_of U hU hne
    · exact continuous_const
    · exact continuous_const

noncomputable def pairedMinimalPoint (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0) :
    ExactFiber 4 6 5 := ⟨pairedMinimalNet U,pairedMinimalNet_eval U hU⟩

theorem continuous_pairedMinimalPoint_of (U : X → Fin 2 → Fin 2 → ℝ) (hU : Continuous U)
    (hne : ∀ x,codeDet (U x)≠0) : Continuous (fun x => pairedMinimalPoint (U x) (hne x)) :=
  (continuous_pairedMinimalNet_of U hU hne).subtype_mk _

#print axioms continuous_pairedMinimalNet_of
#print axioms continuous_pairedMinimalPoint_of
end MaxCaterpillar.Fiber.Count65.Paired
