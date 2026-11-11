import MaxCaterpillar.Fiber.Count65.Paired.ComparatorPath
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointScaledBridge
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms.SwitchingRows
import MaxCaterpillar.Fiber.Count65.Paired.SecondReindex.Prefix

/-! The literal comparator-and-signed-baseline endpoint attaches in the genuine quotient. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
open BigOperators Absorption

theorem quotient_joined_of_joinedIn (a b : ExactFiber 4 6 5)
    (hab : JoinedIn (ExactSet 4 6 5) a.val b.val) :
    Joined (quotientMk a) (quotientMk b) :=
  ⟨hab.joined_subtype.somePath.map quotientMk_continuous⟩

theorem quotient_reindexSecond (a : ExactFiber 4 6 5) (e : Equiv.Perm (Fin 5)) :
    quotientMk (reindexSecondFiber e a) = quotientMk a :=
  (quotientMk_eq_of_step (SymmetryStep.hidden a (Equiv.refl _) e)).symm

noncomputable def comparatorNet (U : Fin 2 → Fin 2 → ℝ) (s : ℝ) (Z : Fin 6 → ℝ) :
    Network 4 6 5 :=
  comparatorWithSpectators (pairedRows U) 0 (comparisonRow U) (baselineRow U)
    0 0 0 (fun _ : Fin 1 => Z) 0 0 s

theorem comparatorNet_exact (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U ≠ 0)
    (s : ℝ) (Z : Fin 6 → ℝ) : ∀ x, (comparatorNet U s Z).eval x = Maximum 4 x := by
  intro x
  have hm := pairedMinimalNet_eval U hdet x
  rw [pairedMinimalNet_eval_formula] at hm
  unfold comparatorNet comparatorWithSpectators
  rw [appendSpectators_eval,comparatorBaselineNet_eval]
  simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,
    preact_pairedRows_zero]
  linarith only [hm]

noncomputable def comparatorPoint (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U ≠ 0)
    (s : ℝ) (Z : Fin 6 → ℝ) : ExactFiber 4 6 5 :=
  ⟨comparatorNet U s Z,comparatorNet_exact U hdet s Z⟩

private theorem physical_ext (a b : Network 4 6 5)
    (hA : a.W₁=b.W₁) (hβ : a.b₁=b.b₁) (hC : a.W₂=b.W₂)
    (hδ : a.b₂=b.b₂) (hd : a.w₃=b.w₃) (hθ : a.b₃=b.b₃) : a=b := by
  cases a
  cases b
  congr 1

theorem clearedComparator_reindex (U : Fin 2 → Fin 2 → ℝ) (Z : Fin 6 → ℝ) :
    permuteHidden (replaceSecond (comparatorNet U 0 Z) 1 0 0)
      (Equiv.refl _) scaledEndpointOrder = scaledEndpointNet U 0 1 Z := by
  apply physical_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;>
      norm_num [permuteHidden,replaceSecond,comparatorNet,comparatorWithSpectators,
        appendSpectators,comparatorBaselineNet,scaledEndpointNet,scaledEndpointOrder,
        Fin.append,Fin.addCases,Function.update,Fin.ext_iff,Fin.ofNat,Fin.ofNat',Fin.castLT,Fin.coe_ofNat_eq_mod] <;> rfl
  · funext i
    fin_cases i
    · change (0 : ℝ)=0
      rfl
    · change (0 : ℝ)+0*0=0
      ring
    · change -((0 : ℝ)+0*0)=0
      ring
    · change (0 : ℝ)=0
      rfl
    · change (0 : ℝ)=0
      rfl
  · funext i
    fin_cases i
    · change (0 : ℝ)=0
      rfl
    · change (1 : ℝ)=1
      rfl
    · change (-1 : ℝ)= -1
      rfl
    · change (1 : ℝ)-0=1
      ring
    · change (0 : ℝ)=0
      rfl
  · rfl

/-- Every real comparator orientation weight attaches to the actual minimal
paired endpoint. The fifth dormant incoming row remains arbitrary. -/
theorem comparator_quotient_joined (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U ≠ 0)
    (s : ℝ) (Z : Fin 6 → ℝ) :
    Joined (quotientMk (comparatorPoint U hdet s Z))
      (quotientMk (pairedMinimalPoint U hdet)) := by
  have hpath := comparatorWithSpectators_joinedIn_exact (pairedRows U) 0
    (comparisonRow U) (baselineRow U) 0 0 0 (fun _ : Fin 1 => Z) 0 0 s 0
    (comparatorNet_exact U hdet s Z)
  have hfirst := quotient_joined_of_joinedIn (comparatorPoint U hdet s Z)
    (comparatorPoint U hdet 0 Z) hpath
  let a := comparatorPoint U hdet 0 Z
  have hz : a.val.w₃ 1 = 0 := rfl
  let b := unusedSecondPoint a 1 hz 0 0 1
  have hsecond : Joined (quotientMk a) (quotientMk b) :=
    ⟨(unusedSecondPath a 1 hz 0 0).map quotientMk_continuous⟩
  have he : permuteHiddenFiber (Equiv.refl _) scaledEndpointOrder b =
      scaledEndpointPoint U hdet 0 1 (by norm_num) Z := by
    apply Subtype.ext
    change permuteHidden (unusedSecondMove a.val 1 0 0 1)
      (Equiv.refl _) scaledEndpointOrder = _
    rw [unusedSecondMove_one]
    exact clearedComparator_reindex U Z
  have hq : quotientMk b = quotientMk (scaledEndpointPoint U hdet 0 1 (by norm_num) Z) := by
    rw [← he]
    exact quotientMk_eq_of_step (SymmetryStep.hidden b (Equiv.refl _) scaledEndpointOrder)
  rw [hq] at hsecond
  exact hfirst.trans (hsecond.trans (scaledEndpoint_quotient_joined U hdet 0 1 (by norm_num) Z))

end MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
