import MaxCaterpillar.Frontier.StarCertificate.XiIntegerData
import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! # Integral arithmetic for the same Xi coefficient computation

All values of the scale-240 dictionary are integers. Computing with them in
Z avoids repeated rational normalization; the cast theorem below connects
this arithmetic directly to Xi's rational semantic linearization.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def starIntegerSubsetForms (j : Fin 15) (i : Fin 4) : ℤ :=
  if Nat.testBit (j.val + 1) i.val then 1 else 0

theorem starIntegerSubsetForms_cast : ∀ (j : Fin 15) (i : Fin 4),
    (starIntegerSubsetForms j i : ℚ) = subsetForms j i :=
  of_decide_eq_true (by with_unfolding_all rfl)

def FormRef.integerForm {m n : ℕ} (A : Fin m → IntegerForm n) : FormRef m → IntegerForm n
  | .zero => 0
  | .pos j => A j
  | .neg j => fun i => -(A j i)

theorem FormRef.integerForm_cast (r : FormRef 15) (i : Fin 4) :
    (r.integerForm starIntegerSubsetForms i : ℚ) = r.form subsetForms i := by
  cases r with
  | zero => rfl
  | pos j => exact starIntegerSubsetForms_cast j i
  | neg j =>
    simp only [FormRef.integerForm, FormRef.form, Int.cast_neg, starIntegerSubsetForms_cast]

def Sign.integerDirection : Sign → ℤ
  | .neg => -1
  | .zero => 0
  | .pos => 1

theorem Sign.integerDirection_cast (s : Sign) : (s.integerDirection : ℚ) = s.direction := by
  cases s <;> norm_num [Sign.integerDirection, Sign.direction]

def starIntegerOmega : IntegerForm 4 := ![10,-20,20,-10]

theorem starIntegerOmega_cast : ∀ j : Fin 4, (starIntegerOmega j : ℚ) = starOmega j :=
  of_decide_eq_true (by with_unfolding_all rfl)

def maskedXiIntegerCoefficients (T : Fin 16) (p : Fin 120) (s : Fin 15 → Sign) :
    IntegerForm 4 :=
  let chainSigns := fun j => (maskedChain T p j).sign s
  let orientation := headSign chainSigns
  let normalized := fun t => normalizeSign orientation ((maskedCoarse T p t).sign s)
  let weights := if Mixed chainSigns then starIntegerKappa normalized else starIntegerOmega
  fun i => ∑ j, (orientation.integerDirection * weights j) *
    (maskedChain T p j).integerForm starIntegerSubsetForms i

theorem maskedXiIntegerCoefficients_cast (T : Fin 16) (p : Fin 120)
    (s : Fin 15 → Sign) (i : Fin 4) :
    (maskedXiIntegerCoefficients T p s i : ℚ) =
      xiCoefficients subsetForms starOmega starKappa (maskedChain T p) (maskedCoarse T p) s i := by
  unfold maskedXiIntegerCoefficients xiCoefficients
  simp only [Int.cast_sum, Int.cast_mul, Sign.integerDirection_cast,
    FormRef.integerForm_cast]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hm : Mixed (fun j => (maskedChain T p j).sign s)
  · simp only [if_pos hm]
    rw [congrFun (starIntegerKappa_cast _) j]
  · simp only [if_neg hm, starIntegerOmega_cast]

def maskedPsiIntegerCoefficients (T P : Fin 16) (s : Fin 15 → Sign) : IntegerForm 4 :=
  fun i => ∑ p : Fin 120,
    if centerBeforeMask p = P then maskedXiIntegerCoefficients T p s i else 0

def componentIntegerCoefficients (S A : Finset (Fin 4)) (s : Fin 15 → Sign) : IntegerForm 4 :=
  fun i => ∑ T in S.powerset, (-1 : ℤ) ^ (S \ T).card *
    ∑ P in (Finset.univ : Finset (Fin 4)).powerset.filter (fun P => P ∩ S = A),
      maskedPsiIntegerCoefficients (setMask T) (setMask P) s i

end MaxCaterpillar.Frontier.StarCertificate
