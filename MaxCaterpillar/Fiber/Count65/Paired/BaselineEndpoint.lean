import MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
import MaxCaterpillar.Fiber.Count65.Paired.BaselineLift

/-! # Globally nonnegative physical carrier rows at baseline fold endpoints

Both folding routes end in the same physical form: every endpoint row is a
linear combination of two globally nonnegative preactivations whose signed
difference is the original weighted baseline. These declarations expose this
form directly for the finite quadrant attachment argument.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineEndpoint
open BigOperators Frontier Absorption BaselineOrdinary
variable {m : ℕ}

lemma preact_linear (U : Fin 2 → Fin 2 → ℝ) (Q R : Fin 6 → ℝ) (a b : ℝ) (x : Point 4) :
    preact (pairedRows U) 0 (fun j => a*Q j+b*R j) 0 x=
      a*preact (pairedRows U) 0 Q 0 x+b*preact (pairedRows U) 0 R 0 x := by
  simp only [preact,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum,
    Pi.zero_apply,add_zero]

lemma preact_sub (U : Fin 2 → Fin 2 → ℝ) (Q R : Fin 6 → ℝ) (x : Point 4) :
    preact (pairedRows U) 0 (fun j => Q j-R j) 0 x=
      preact (pairedRows U) 0 Q 0 x-preact (pairedRows U) 0 R 0 x := by
  simpa only [one_mul,neg_one_mul,sub_eq_add_neg] using preact_linear U Q R 1 (-1) x

def ordinaryQRow (swap : Bool) (A B c d : ℝ) : Fin 6 → ℝ :=
  permRow swap (liftTwoRow A B c d 1 0)

def ordinaryRRow (swap : Bool) (A B c d : ℝ) : Fin 6 → ℝ :=
  permRow swap (liftTwoRow A B c d 0 1)

private lemma permRow_linear (swap : Bool) (Q R : Fin 6 → ℝ) (a b : ℝ) :
    permRow swap (fun j => a*Q j+b*R j)=
      (fun j => a*permRow swap Q j+b*permRow swap R j) := by
  cases swap
  · rfl
  · funext j
    fin_cases j <;> rfl

lemma ordinary_row_factor (swap : Bool) (A B c d a b : ℝ) :
    permRow swap (liftTwoRow A B c d a b)=
      (fun j => a*ordinaryQRow swap A B c d j+b*ordinaryRRow swap A B c d j) := by
  have h : liftTwoRow A B c d a b=
      (fun j => a*liftTwoRow A B c d 1 0 j+b*liftTwoRow A B c d 0 1 j) := by
    funext j
    fin_cases j <;> simp [liftTwoRow,liftThreeRow]
  rw [h]
  exact permRow_linear swap _ _ a b

lemma ordinaryQRow_preact (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d : ℝ) (x : Point 4) :
    preact (pairedRows U) 0 (ordinaryQRow swap A B c d) 0 x=
      BaselineOrdinary.positiveCoordinate U swap A B c d x := by
  simp only [preact,Pi.zero_apply,add_zero,BaselineFold.first_activation,
    ordinaryQRow,dot_permRow]
  change (∑ j, liftTwoRow A B c d 1 0 j*orderedFeatures U swap x j)=_
  rw [actualRow_dot]
  ring

lemma ordinaryRRow_preact (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d : ℝ) (x : Point 4) :
    preact (pairedRows U) 0 (ordinaryRRow swap A B c d) 0 x=
      BaselineOrdinary.negativeCoordinate U c d x := by
  simp only [preact,Pi.zero_apply,add_zero,BaselineFold.first_activation,
    ordinaryRRow,dot_permRow]
  change (∑ j, liftTwoRow A B c d 0 1 j*orderedFeatures U swap x j)=_
  rw [actualRow_dot]
  ring

theorem ordinary_carriers_nonneg (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d : ℝ) (hA : 0≤A) (hB : 0≤B) (x : Point 4) :
    0≤preact (pairedRows U) 0 (ordinaryQRow swap A B c d) 0 x ∧
      0≤preact (pairedRows U) 0 (ordinaryRRow swap A B c d) 0 x := by
  rw [ordinaryQRow_preact,ordinaryRRow_preact]
  exact BaselineOrdinary.coordinates_nonneg U swap A B c d hA hB x

theorem ordinary_carriers_subtract (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d : ℝ) (x : Point 4) :
    preact (pairedRows U) 0
      (fun j => ordinaryQRow swap A B c d j-ordinaryRRow swap A B c d j) 0 x=
        orderedTarget U swap A B c d x := by
  rw [preact_sub,ordinaryQRow_preact,ordinaryRRow_preact]
  exact (BaselineOrdinary.target_coordinates U swap A B c d x).symm

theorem ordinary_endpoint_row_factor (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d : ℝ) (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ) (k : Fin m) :
    (endpointNet U swap A B c d C bias weights θ).W₂ k=
      (fun j => carrierCoefficients A C k*ordinaryQRow swap A B c d j+
        endpointCoefficients c d C k*ordinaryRRow swap A B c d j) :=
  ordinary_row_factor swap A B c d (carrierCoefficients A C k) (endpointCoefficients c d C k)

theorem ordinary_weighted_carriers_subtract (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d s : ℝ)
    (h : ∀ x, orderedTarget U swap A B c d x=BaselineWeighted.weightedTarget s x) (x : Point 4) :
    preact (pairedRows U) 0
      (fun j => ordinaryQRow swap A B c d j-ordinaryRRow swap A B c d j) 0 x=
        BaselineWeighted.weightedTarget s x :=
  (ordinary_carriers_subtract U swap A B c d x).trans (h x)

def mixedQRow (A B c d ε : ℝ) : Fin 6 → ℝ :=
  if ε=1 then BaselineLift.liftRow A B c d 1 0 else BaselineLift.liftRow A B c d 0 1

def mixedRRow (A B c d ε : ℝ) : Fin 6 → ℝ :=
  if ε=1 then BaselineLift.liftRow A B c d 0 1 else BaselineLift.liftRow A B c d 1 0

def mixedFirstCoefficient (A B ε : ℝ) (W : Fin 6 → ℝ) : ℝ := if ε=1 then W 0/A else W 1/B
def mixedSecondCoefficient (A B ε : ℝ) (W : Fin 6 → ℝ) : ℝ := if ε=1 then W 1/B else W 0/A

lemma mixed_lift_preact (U : Fin 2 → Fin 2 → ℝ) (A B c d a b : ℝ) (x : Point 4) :
    preact (pairedRows U) 0 (BaselineLift.liftRow A B c d a b) 0 x=
      a*BaselineFold.positiveCoordinate U A c d x+b*BaselineFold.negativeCoordinate U B c d x := by
  simp only [preact,Pi.zero_apply,add_zero,BaselineFold.first_activation]
  exact BaselineLift.liftRow_dot U A B c d a b x

lemma mixed_row_linear (A B c d a b : ℝ) :
    BaselineLift.liftRow A B c d a b=
      (fun j => a*BaselineLift.liftRow A B c d 1 0 j+
        b*BaselineLift.liftRow A B c d 0 1 j) := by
  funext j
  fin_cases j <;> simp [BaselineLift.liftRow]

theorem mixed_endpoint_row_factor (A B c d ε : ℝ) (hA : A≠0) (hB : B≠0) (W : Fin 6 → ℝ) :
    BaselineFold.foldRow A B c d 1 W=
      (fun j => mixedFirstCoefficient A B ε W*mixedQRow A B c d ε j+
        mixedSecondCoefficient A B ε W*mixedRRow A B c d ε j) := by
  rw [BaselineLift.foldRow_one_eq_liftRow A B c d hA hB,mixed_row_linear]
  by_cases hε : ε=1
  · simp only [mixedFirstCoefficient,mixedSecondCoefficient,mixedQRow,mixedRRow,hε,if_true]
  · simp only [mixedFirstCoefficient,mixedSecondCoefficient,mixedQRow,mixedRRow,hε,if_false]
    funext j
    ring

theorem mixed_physical_endpoint_row_factor (U : Fin 2 → Fin 2 → ℝ) (A B c d ε : ℝ)
    (hA : A≠0) (hB : B≠0) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ) (k : Fin m) :
    (BaselineFold.foldedCompletion U A B c d C bias weights θ 1).W₂ k=
      (fun j => mixedFirstCoefficient A B ε (C k)*mixedQRow A B c d ε j+
        mixedSecondCoefficient A B ε (C k)*mixedRRow A B c d ε j) :=
  mixed_endpoint_row_factor A B c d ε hA hB (C k)

theorem mixed_carriers_nonneg (U : Fin 2 → Fin 2 → ℝ) (A B c d ε : ℝ)
    (hA : 0≤A) (hB : 0≤B) (x : Point 4) :
    0≤preact (pairedRows U) 0 (mixedQRow A B c d ε) 0 x ∧
      0≤preact (pairedRows U) 0 (mixedRRow A B c d ε) 0 x := by
  have h := BaselineFold.coordinates_nonneg U A B c d hA hB x
  by_cases hε : ε=1
  · simpa only [mixedQRow,mixedRRow,hε,if_true,mixed_lift_preact,
      one_mul,zero_mul,add_zero,zero_add] using h
  · simpa only [mixedQRow,mixedRRow,hε,if_false,mixed_lift_preact,
      one_mul,zero_mul,add_zero,zero_add] using And.intro h.2 h.1

theorem mixed_carriers_subtract (U : Fin 2 → Fin 2 → ℝ) (A B c d ε : ℝ)
    (hε : ε=1 ∨ ε=-1) (x : Point 4) :
    preact (pairedRows U) 0 (fun j => mixedQRow A B c d ε j-mixedRRow A B c d ε j) 0 x=
      ε*BaselineFold.target U A B c d x := by
  rw [preact_sub]
  rcases hε with rfl|rfl
  · simp only [mixedQRow,mixedRRow,if_true,mixed_lift_preact,one_mul,zero_mul,add_zero,zero_add]
    exact (BaselineFold.target_coordinates U A B c d x).symm
  · norm_num only [mixedQRow,mixedRRow,show (-1:ℝ)≠1 by norm_num,if_false,
      mixed_lift_preact,one_mul,zero_mul,add_zero,zero_add,neg_one_mul]
    rw [BaselineFold.target_coordinates]
    ring

theorem mixed_weighted_carriers_subtract (U : Fin 2 → Fin 2 → ℝ) (A B c d ε s : ℝ)
    (hε : ε=1 ∨ ε=-1)
    (h : ∀ x, BaselineWeighted.weightedTarget s x=ε*BaselineFold.target U A B c d x) (x : Point 4) :
    preact (pairedRows U) 0 (fun j => mixedQRow A B c d ε j-mixedRRow A B c d ε j) 0 x=
      BaselineWeighted.weightedTarget s x :=
  (mixed_carriers_subtract U A B c d ε hε x).trans (h x).symm

end MaxCaterpillar.Fiber.Count65.Paired.BaselineEndpoint
