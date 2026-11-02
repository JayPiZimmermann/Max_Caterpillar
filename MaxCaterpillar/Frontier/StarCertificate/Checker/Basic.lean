import MaxCaterpillar.Frontier.Basic

/-! # Rational linear-form sign certificates

All finite data are rational. Their meaning is evaluation on arbitrary real
vectors, including every equality boundary.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

inductive Sign where
  | neg
  | zero
  | pos
  deriving DecidableEq, Repr

instance : Fintype Sign where
  elems := {.neg, .zero, .pos}
  complete s := by cases s <;> simp

def Sign.Holds (s : Sign) (a : ℝ) : Prop :=
  match s with
  | .neg => a < 0
  | .zero => a = 0
  | .pos => 0 < a

noncomputable def signOf (a : ℝ) : Sign :=
  if a < 0 then .neg else if a = 0 then .zero else .pos

theorem signOf_holds (a : ℝ) : (signOf a).Holds a := by
  unfold signOf
  split_ifs with hn hz
  · exact hn
  · exact hz
  · exact lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hz)

theorem Sign.eq_signOf {s : Sign} {a : ℝ} (h : s.Holds a) : s = signOf a := by
  cases s with
  | neg =>
    change a < 0 at h
    simp only [signOf, if_pos h]
  | zero =>
    change a = 0 at h
    subst a
    simp [signOf]
  | pos =>
    change 0 < a at h
    simp only [signOf, if_neg (not_lt.mpr h.le), if_neg h.ne']

abbrev RationalForm (n : ℕ) := Fin n → ℚ
abbrev Context (m : ℕ) := Fin m → Option Sign

def evalForm {n : ℕ} (a : RationalForm n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (a i : ℝ) * x i

def Holds {m n : ℕ} (A : Fin m → RationalForm n) (p : Context m)
    (x : Fin n → ℝ) : Prop :=
  ∀ j s, p j = some s → s.Holds (evalForm (A j) x)

noncomputable def actualSigns {m n : ℕ} (A : Fin m → RationalForm n) (x : Fin n → ℝ) : Fin m → Sign :=
  fun j => signOf (evalForm (A j) x)

def contextSigns {m : ℕ} (p : Context m) : Fin m → Sign :=
  fun j => (p j).getD .zero

def Complete {m : ℕ} (p : Context m) : Prop := ∀ j, ∃ s, p j = some s

instance completeDecidable {m : ℕ} (p : Context m) : Decidable (Complete p) := by
  unfold Complete
  infer_instance

def emptyContext (m : ℕ) : Context m := fun _ => none

theorem holds_empty {m n : ℕ} (A : Fin m → RationalForm n) (x : Fin n → ℝ) :
    Holds A (emptyContext m) x := by
  intro j s hs
  cases hs

theorem holds_update {m n : ℕ} (A : Fin m → RationalForm n) (p : Context m)
    (x : Fin n → ℝ) (hp : Holds A p x) (j : Fin m) (s : Sign)
    (hs : s.Holds (evalForm (A j) x)) :
    Holds A (Function.update p j (some s)) x := by
  intro k t hk
  by_cases hkj : k = j
  · subst k
    simp only [Function.update_same, Option.some.injEq] at hk
    subst t
    exact hs
  · rw [Function.update_noteq hkj] at hk
    exact hp k t hk

theorem complete_signs_eq_actual {m n : ℕ} (A : Fin m → RationalForm n)
    (p : Context m) (x : Fin n → ℝ) (hc : Complete p) (hp : Holds A p x) :
    contextSigns p = actualSigns A x := by
  funext j
  obtain ⟨s, hs⟩ := hc j
  have he := Sign.eq_signOf (hp j s hs)
  simpa only [contextSigns, hs, Option.getD_some, actualSigns] using he

theorem evalForm_combination {m n : ℕ} (A : Fin m → RationalForm n)
    (w : Fin m → ℚ) (x : Fin n → ℝ) :
    evalForm (fun i => ∑ j, w j * A j i) x = ∑ j, (w j : ℝ) * evalForm (A j) x := by
  simp only [evalForm, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem evalForm_zero {n : ℕ} (x : Fin n → ℝ) : evalForm (0 : RationalForm n) x = 0 := by
  simp only [evalForm, Pi.zero_apply, Rat.cast_zero, zero_mul, Finset.sum_const_zero]

def oriented {m n : ℕ} (A : Fin m → RationalForm n) (p : Context m) (j : Fin m) :
    RationalForm n :=
  if p j = some .neg then fun i => -(A j i) else A j

theorem evalForm_oriented_neg {m n : ℕ} (A : Fin m → RationalForm n)
    (p : Context m) (j : Fin m) (x : Fin n → ℝ) (hj : p j = some .neg) :
    evalForm (oriented A p j) x = -evalForm (A j) x := by
  unfold oriented
  rw [if_pos hj]
  simp only [evalForm, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]

theorem evalForm_oriented_other {m n : ℕ} (A : Fin m → RationalForm n)
    (p : Context m) (j : Fin m) (x : Fin n → ℝ) (hj : p j ≠ some .neg) :
    evalForm (oriented A p j) x = evalForm (A j) x := by
  simp only [oriented, if_neg hj]

end MaxCaterpillar.Frontier.StarCertificate
