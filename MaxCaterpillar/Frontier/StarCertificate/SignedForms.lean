import MaxCaterpillar.Frontier.StarCertificate.Checker.Basic

/-! # Signed references to the tested rational forms

A reference is zero, one tested form, or its negative. This is the semantic
bridge used by the star certificate: all chamber coordinates and all coarse
resonance tests are signed subset sums.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def Sign.opposite : Sign → Sign
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

theorem Sign.opposite_holds {s : Sign} {a : ℝ} (h : s.Holds a) :
    s.opposite.Holds (-a) := by
  cases s <;> simp only [Sign.Holds, Sign.opposite] at * <;> linarith

theorem signOf_neg (a : ℝ) : signOf (-a) = (signOf a).opposite :=
  (Sign.eq_signOf (Sign.opposite_holds (signOf_holds a))).symm

@[simp] theorem signOf_zero : signOf 0 = .zero := by
  simp [signOf]

inductive FormRef (m : ℕ) where
  | zero
  | pos (j : Fin m)
  | neg (j : Fin m)
  deriving DecidableEq, Repr

def FormRef.form {m n : ℕ} (A : Fin m → RationalForm n) : FormRef m → RationalForm n
  | .zero => 0
  | .pos j => A j
  | .neg j => fun i => -(A j i)

def FormRef.sign {m : ℕ} (p : Fin m → Sign) : FormRef m → Sign
  | .zero => .zero
  | .pos j => p j
  | .neg j => (p j).opposite

theorem evalForm_neg {n : ℕ} (a : RationalForm n) (x : Fin n → ℝ) :
    evalForm (fun i => -(a i)) x = -evalForm a x := by
  simp only [evalForm, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]

/-- The sign of every signed reference is determined by the tested forms,
for every real input, with the zero case included. -/
theorem FormRef.actual_sign {m n : ℕ} (A : Fin m → RationalForm n)
    (x : Fin n → ℝ) (r : FormRef m) :
    signOf (evalForm (r.form A) x) = r.sign (actualSigns A x) := by
  cases r with
  | zero => simp only [FormRef.form, evalForm_zero, signOf_zero, FormRef.sign]
  | pos j => rfl
  | neg j => simp only [FormRef.form, evalForm_neg, signOf_neg, FormRef.sign, actualSigns]

/-- A rational linear combination of referenced forms evaluates to the
corresponding real linear combination. -/
theorem evalForm_ref_combination {m n r : ℕ} (A : Fin m → RationalForm n)
    (refs : Fin r → FormRef m) (w : Fin r → ℚ) (x : Fin n → ℝ) :
    evalForm (fun i => ∑ j, w j * ((refs j).form A i)) x =
      ∑ j, (w j : ℝ) * evalForm ((refs j).form A) x := by
  exact evalForm_combination (fun j => (refs j).form A) w x

end MaxCaterpillar.Frontier.StarCertificate
