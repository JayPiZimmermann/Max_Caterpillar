import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointNetwork
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointCodes
import MaxCaterpillar.Fiber.Symmetry

/-! # Determinant-sign reflection is an actual first-hidden permutation -/
set_option autoImplicit false
set_option maxHeartbeats 40000
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired

lemma inverseCode_reverse_00 (U : Code) : inverseCode (reverseCode U) 0 0=inverseCode U 0 0 := by
  change (-U 1 1)/codeDet (reverseCode U)=U 1 1/codeDet U
  rw [codeDet_reverseCode U]
  exact neg_div_neg_eq _ _
lemma inverseCode_reverse_01 (U : Code) : inverseCode (reverseCode U) 0 1= -inverseCode U 0 1 := by
  change (-U 0 1)/codeDet (reverseCode U)= -(-U 0 1/codeDet U)
  rw [codeDet_reverseCode U]
  simpa only [neg_div,neg_neg] using (neg_div_neg_eq (U 0 1) (codeDet U))
lemma inverseCode_reverse_10 (U : Code) : inverseCode (reverseCode U) 1 0=inverseCode U 1 0 := by
  change (-(-U 1 0))/codeDet (reverseCode U)= -U 1 0/codeDet U
  rw [codeDet_reverseCode U]
  simp only [neg_neg,div_neg_eq_neg_div,neg_div]
lemma inverseCode_reverse_11 (U : Code) : inverseCode (reverseCode U) 1 1= -inverseCode U 1 1 := by
  change U 0 0/codeDet (reverseCode U)= -(U 0 0/codeDet U)
  rw [codeDet_reverseCode U]
  exact div_neg_eq_neg_div _ _

def reverseCodePermutation : Equiv.Perm (Fin 6) := Equiv.swap 4 5

lemma pairedRows_reverseCode (U : Code) :
    pairedRows (reverseCode U)=fun j i => pairedRows U (reverseCodePermutation j) i := by
  funext j
  fin_cases j
  · change (![1,-1,0,0] : Point 4)=![1,-1,0,0]; rfl
  · change (![0,0,1,-1] : Point 4)=![0,0,1,-1]; rfl
  · change (![0,U 0 0,0,U 0 1] : Point 4)=![0,U 0 0,0,U 0 1]; rfl
  · change (![0,-U 0 0,0,-U 0 1] : Point 4)=![0,-U 0 0,0,-U 0 1]; rfl
  · change (![0,-U 1 0,0,-U 1 1] : Point 4)=![0,-U 1 0,0,-U 1 1]; rfl
  · change (![0,-(-U 1 0),0,-(-U 1 1)] : Point 4)=![0,U 1 0,0,U 1 1]
    simp only [neg_neg]

lemma baselineRow_reverseCode (U : Code) :
    baselineRow (reverseCode U)=fun j => baselineRow U (reverseCodePermutation j) := by
  funext j
  fin_cases j
  · change (0 : ℝ)=0; rfl
  · change (1 : ℝ)=1; rfl
  · change inverseCode (reverseCode U) 1 0=inverseCode U 1 0
    exact inverseCode_reverse_10 U
  · change -inverseCode (reverseCode U) 1 0= -inverseCode U 1 0
    exact congrArg Neg.neg (inverseCode_reverse_10 U)
  · change inverseCode (reverseCode U) 1 1= -inverseCode U 1 1
    exact inverseCode_reverse_11 U
  · change -inverseCode (reverseCode U) 1 1=inverseCode U 1 1
    rw [inverseCode_reverse_11,neg_neg]

lemma comparisonRow_reverseCode (U : Code) :
    comparisonRow (reverseCode U)=fun j => comparisonRow U (reverseCodePermutation j) := by
  funext j
  fin_cases j
  · change (1 : ℝ)=1; rfl
  · change (-1 : ℝ)= -1; rfl
  · change inverseCode (reverseCode U) 0 0-inverseCode (reverseCode U) 1 0=
      inverseCode U 0 0-inverseCode U 1 0
    rw [inverseCode_reverse_00,inverseCode_reverse_10]
  · change -(inverseCode (reverseCode U) 0 0-inverseCode (reverseCode U) 1 0)=
      -(inverseCode U 0 0-inverseCode U 1 0)
    rw [inverseCode_reverse_00,inverseCode_reverse_10]
  · change inverseCode (reverseCode U) 0 1-inverseCode (reverseCode U) 1 1=
      -(inverseCode U 0 1-inverseCode U 1 1)
    rw [inverseCode_reverse_01,inverseCode_reverse_11]
    ring
  · change -(inverseCode (reverseCode U) 0 1-inverseCode (reverseCode U) 1 1)=
      inverseCode U 0 1-inverseCode U 1 1
    rw [inverseCode_reverse_01,inverseCode_reverse_11]
    ring

lemma pairedMinimal_second_reverseCode (U : Code) :
    (pairedMinimalNet (reverseCode U)).W₂=
      fun k j => (pairedMinimalNet U).W₂ k (reverseCodePermutation j) := by
  funext k j
  fin_cases k
  · change baselineRow (reverseCode U) j=baselineRow U (reverseCodePermutation j)
    exact congrFun (baselineRow_reverseCode U) j
  · change -baselineRow (reverseCode U) j= -baselineRow U (reverseCodePermutation j)
    exact congrArg Neg.neg (congrFun (baselineRow_reverseCode U) j)
  · change comparisonRow (reverseCode U) j=comparisonRow U (reverseCodePermutation j)
    exact congrFun (comparisonRow_reverseCode U) j
  · change (0 : ℝ)=0; rfl
  · change (0 : ℝ)=0; rfl

/-- Equality of every physical array realizes determinant-sign reflection by
one permitted first-hidden-neuron permutation. -/
theorem pairedMinimalNet_reverseCode (U : Code) :
    pairedMinimalNet (reverseCode U)=
      permuteHidden (pairedMinimalNet U) (Equiv.swap (4 : Fin 6) 5) (Equiv.refl _) := by
  let F : (Fin 6 → Point 4) → (Fin 5 → Fin 6 → ℝ) → Network 4 6 5 :=
    fun A C => ⟨A,0,C,0,![1,-1,1,0,0],0⟩
  change F (pairedRows (reverseCode U)) ((pairedMinimalNet (reverseCode U)).W₂)=
    F (fun j i => pairedRows U (reverseCodePermutation j) i)
      (fun k j => (pairedMinimalNet U).W₂ k (reverseCodePermutation j))
  exact congrArg₂ F (pairedRows_reverseCode U) (pairedMinimal_second_reverseCode U)

#print axioms pairedMinimalNet_reverseCode
end MaxCaterpillar.Fiber.Count65.Paired
