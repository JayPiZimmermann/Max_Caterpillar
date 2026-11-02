import MaxCaterpillar.Frontier.StarCertificate.Checker.Integer

/-! # Small Boolean folds for generated integer certificates

The folds avoid building a finite-set quantifier decision procedure at
every arithmetic entry. Their equivalences are proved for all sizes.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def finAll : (n : ℕ) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n+1, f => f 0 && finAll n (fun i => f i.succ)

def finAny : (n : ℕ) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n+1, f => f 0 || finAny n (fun i => f i.succ)

def intSum : (n : ℕ) → (Fin n → ℤ) → ℤ
  | 0, _ => 0
  | n+1, f => f 0 + intSum n (fun i => f i.succ)

theorem finAll_eq_true (n : ℕ) (f : Fin n → Bool) :
    finAll n f = true ↔ ∀ i, f i = true := by
  induction n with
  | zero => simp [finAll]
  | succ n ih => simp only [finAll, Bool.and_eq_true, ih, Fin.forall_fin_succ]

theorem finAny_eq_true (n : ℕ) (f : Fin n → Bool) :
    finAny n f = true ↔ ∃ i, f i = true := by
  induction n with
  | zero => simp [finAny]
  | succ n ih => simp only [finAny, Bool.or_eq_true, ih, Fin.exists_fin_succ]

theorem intSum_eq_sum (n : ℕ) (f : Fin n → ℤ) : intSum n f = ∑ i, f i := by
  induction n with
  | zero => simp only [intSum, Fin.sum_univ_zero]
  | succ n ih => simp only [intSum, ih, Fin.sum_univ_succ]

def completeCheck {m : ℕ} (p : Context m) : Bool :=
  finAll m (fun j => (p j).isSome)

theorem completeCheck_eq_true {m : ℕ} (p : Context m) :
    completeCheck p = true ↔ Complete p := by
  rw [completeCheck, finAll_eq_true]
  apply forall_congr'
  intro j
  cases hj : p j <;> simp [Complete, hj]

def strictNonnegCheck (s : Option Sign) (w : ℤ) : Bool :=
  match s with
  | some .neg | some .pos => decide (0 ≤ w)
  | _ => true

theorem strictNonnegCheck_eq_true (s : Option Sign) (w : ℤ) :
    strictNonnegCheck s w = true ↔ ∀ t, s = some t → t ≠ .zero → 0 ≤ w := by
  cases s with
  | none => simp [strictNonnegCheck]
  | some s => cases s <;> simp [strictNonnegCheck]

def strictPositiveCheck (s : Option Sign) (w : ℤ) : Bool :=
  match s with
  | some .neg | some .pos => decide (0 < w)
  | _ => false

theorem strictPositiveCheck_eq_true (s : Option Sign) (w : ℤ) :
    strictPositiveCheck s w = true ↔ ∃ t, s = some t ∧ t ≠ .zero ∧ 0 < w := by
  cases s with
  | none => simp [strictPositiveCheck]
  | some s => cases s <;> simp [strictPositiveCheck]

def integerFarkasCheck {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : Context m)
    (w : Fin m → ℤ) : Bool :=
  finAll m (fun j => decide (p j = none → w j = 0)) &&
  (finAll m (fun j => strictNonnegCheck (p j) (w j)) &&
  (finAny m (fun j => strictPositiveCheck (p j) (w j)) &&
  finAll n (fun i => decide (intSum m (fun j => w j * integerOriented A p j i) = 0))))

theorem integerFarkasCheck_eq_true {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (p : Context m) (w : Fin m → ℤ) :
    integerFarkasCheck A p w = true ↔ IntegerFarkasValid A p w := by
  simp only [integerFarkasCheck, Bool.and_eq_true, finAll_eq_true, finAny_eq_true,
    decide_eq_true_eq, strictNonnegCheck_eq_true, strictPositiveCheck_eq_true,
    intSum_eq_sum, IntegerFarkasValid]

def integerZeroSpanCheck {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : Context m)
    (a : Fin n → ℤ) (den : ℤ) (w : Fin m → ℤ) : Bool :=
  decide (0 < den) &&
  (if finAll m (fun j => decide (w j = 0)) = true then
    finAll n (fun i => decide (a i = 0))
  else
    finAll m (fun j => decide (p j ≠ some .zero → w j = 0)) &&
    finAll n (fun i => decide (den * a i = intSum m (fun j => w j * A j i))))

theorem integerZeroSpanCheck_eq_true {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (p : Context m) (a : Fin n → ℤ) (den : ℤ) (w : Fin m → ℤ) :
    integerZeroSpanCheck A p a den w = true ↔ IntegerZeroSpanValid A p a den w := by
  unfold integerZeroSpanCheck
  rw [Bool.and_eq_true, decide_eq_true_eq]
  by_cases hz : finAll m (fun j => decide (w j = 0)) = true
  · rw [if_pos hz, finAll_eq_true]
    have hw : ∀ j, w j = 0 := by
      simpa only [decide_eq_true_eq] using (finAll_eq_true m _).mp hz
    constructor
    · rintro ⟨hd, ha⟩
      refine ⟨hd, fun j _ => hw j, fun i => ?_⟩
      have hai : a i = 0 := of_decide_eq_true (ha i)
      simp only [hai, mul_zero, hw, zero_mul, Finset.sum_const_zero]
    · intro h
      refine ⟨h.1, fun i => ?_⟩
      apply decide_eq_true
      have he := h.2.2 i
      simp only [hw, zero_mul, Finset.sum_const_zero] at he
      exact (mul_eq_zero.mp he).resolve_left (ne_of_gt h.1)
  · rw [if_neg hz]
    simp only [Bool.and_eq_true, finAll_eq_true, decide_eq_true_eq, intSum_eq_sum,
      IntegerZeroSpanValid]

def integerSolvedCheck {m n k : ℕ} (A : Fin m → Fin n → ℤ) (p : Context m)
    (a : Fin k → Fin n → ℤ) (den : Fin k → ℤ) (w : Fin k → Fin m → ℤ) : Bool :=
  completeCheck p && finAll k (fun t => integerZeroSpanCheck A p (a t) (den t) (w t))

theorem integerSolvedCheck_eq_true {m n k : ℕ} (A : Fin m → Fin n → ℤ)
    (p : Context m) (a : Fin k → Fin n → ℤ) (den : Fin k → ℤ) (w : Fin k → Fin m → ℤ) :
    integerSolvedCheck A p a den w = true ↔
      Complete p ∧ ∀ t, IntegerZeroSpanValid A p (a t) (den t) (w t) := by
  simp only [integerSolvedCheck, Bool.and_eq_true, completeCheck_eq_true, finAll_eq_true,
    integerZeroSpanCheck_eq_true]

end MaxCaterpillar.Frontier.StarCertificate
