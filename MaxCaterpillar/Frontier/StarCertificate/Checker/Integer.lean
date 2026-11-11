import MaxCaterpillar.Frontier.StarCertificate.Checker.Farkas

/-! # Integer-cleared arithmetic for rational certificate data

These adapters let generated numeric proofs use integer arithmetic. All
meaning is still supplied by the arbitrary-real rational checker.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def integerForms {m n : ℕ} (A : Fin m → Fin n → ℤ) : Fin m → RationalForm n :=
  fun j i => (A j i : ℚ)

def integerOriented {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : Context m) (j : Fin m) :
    Fin n → ℤ :=
  if p j = some .neg then fun i => -(A j i) else A j

theorem oriented_integerForms {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (p : Context m) (j : Fin m) (i : Fin n) :
    oriented (integerForms A) p j i = (integerOriented A p j i : ℚ) := by
  unfold oriented integerOriented integerForms
  split_ifs <;> simp only [Int.cast_neg]

def IntegerFarkasValid {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : Context m)
    (w : Fin m → ℤ) : Prop :=
  (∀ j, p j = none → w j = 0) ∧
  (∀ j s, p j = some s → s ≠ .zero → 0 ≤ w j) ∧
  (∃ j s, p j = some s ∧ s ≠ .zero ∧ 0 < w j) ∧
  (∀ i, ∑ j, w j * integerOriented A p j i = 0)

instance integerFarkasValidDecidable {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (p : Context m) (w : Fin m → ℤ) : Decidable (IntegerFarkasValid A p w) := by
  unfold IntegerFarkasValid
  infer_instance

theorem rational_farkas_of_integer {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (p : Context m) (w : Fin m → ℤ) (h : IntegerFarkasValid A p w) :
    FarkasValid (integerForms A) p (fun j => (w j : ℚ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    change (w j : ℚ) = 0
    rw [h.1 j hj, Int.cast_zero]
  · intro j s hj hs
    change (0 : ℚ) ≤ (w j : ℚ)
    exact_mod_cast h.2.1 j s hj hs
  · obtain ⟨j,s,hj,hs,hw⟩ := h.2.2.1
    refine ⟨j,s,hj,hs,?_⟩
    change (0 : ℚ) < (w j : ℚ)
    exact_mod_cast hw
  · intro i
    simp_rw [oriented_integerForms]
    exact_mod_cast h.2.2.2 i

def IntegerZeroSpanValid {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : Context m)
    (a : Fin n → ℤ) (den : ℤ) (w : Fin m → ℤ) : Prop :=
  0 < den ∧ (∀ j, p j ≠ some .zero → w j = 0) ∧
  (∀ i, den * a i = ∑ j, w j * A j i)

instance integerZeroSpanValidDecidable {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (p : Context m) (a : Fin n → ℤ) (den : ℤ) (w : Fin m → ℤ) :
    Decidable (IntegerZeroSpanValid A p a den w) := by
  unfold IntegerZeroSpanValid
  infer_instance

theorem rational_zeroSpan_of_integer {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (p : Context m) (a : Fin n → ℤ) (den : ℤ) (w : Fin m → ℤ)
    (h : IntegerZeroSpanValid A p a den w) :
    ZeroSpanValid (integerForms A) p (fun i => (a i : ℚ))
      (fun j => (w j : ℚ) / (den : ℚ)) := by
  have hd : (den : ℚ) ≠ 0 := by
    have hp : (0 : ℚ) < den := by exact_mod_cast h.1
    exact hp.ne'
  refine ⟨?_, ?_⟩
  · intro j hj
    change (w j : ℚ) / (den : ℚ) = 0
    rw [h.2.1 j hj, Int.cast_zero, zero_div]
  · intro i
    change (a i : ℚ) = ∑ j, ((w j : ℚ) / (den : ℚ)) * (A j i : ℚ)
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    apply (eq_div_iff hd).mpr
    have he : (den : ℚ) * (a i : ℚ) = ∑ j, (w j : ℚ) * (A j i : ℚ) := by
      exact_mod_cast h.2.2 i
    simpa only [mul_comm] using he

end MaxCaterpillar.Frontier.StarCertificate
