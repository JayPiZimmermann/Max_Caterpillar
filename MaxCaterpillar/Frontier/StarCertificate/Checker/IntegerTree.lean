import MaxCaterpillar.Frontier.StarCertificate.Checker.Tree
import MaxCaterpillar.Frontier.StarCertificate.Checker.FastInteger

/-! # A tree checker whose finite arithmetic is entirely integral -/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate

inductive IntegerCertificateTree (m k : ℕ) where
  | solved (denominators : Fin k → ℤ) (multipliers : Fin k → Fin m → ℤ)
  | impossible (weights : Fin m → ℤ)
  | split (j : Fin m) (neg zero pos : IntegerCertificateTree m k)

def IntegerCertificateTree.rational {m k : ℕ} :
    IntegerCertificateTree m k → CertificateTree m k
  | .solved d w => .solved (fun t j => (w t j : ℚ) / (d t : ℚ))
  | .impossible w => .impossible (fun j => (w j : ℚ))
  | .split j neg zero pos => .split j neg.rational zero.rational pos.rational

def IntegerCertificateTree.Valid {m n k : ℕ} (A : Fin m → Fin n → ℤ)
    (C : (Fin m → Sign) → Fin k → Fin n → ℤ) (p : Context m) :
    IntegerCertificateTree m k → Prop
  | .solved d w => Complete p ∧ ∀ t, IntegerZeroSpanValid A p (C (contextSigns p) t) (d t) (w t)
  | .impossible w => IntegerFarkasValid A p w
  | .split j neg zero pos =>
      neg.Valid A C (Function.update p j (some .neg)) ∧
      zero.Valid A C (Function.update p j (some .zero)) ∧
      pos.Valid A C (Function.update p j (some .pos))

def IntegerCertificateTree.check {m n k : ℕ} (A : Fin m → Fin n → ℤ)
    (C : (Fin m → Sign) → Fin k → Fin n → ℤ) (p : Context m) :
    IntegerCertificateTree m k → Bool
  | .solved d w => completeCheck p &&
      finAll k (fun t => integerZeroSpanCheck A p (C (contextSigns p) t) (d t) (w t))
  | .impossible w => integerFarkasCheck A p w
  | .split j neg zero pos =>
      neg.check A C (Function.update p j (some .neg)) &&
      (zero.check A C (Function.update p j (some .zero)) &&
      pos.check A C (Function.update p j (some .pos)))

theorem IntegerCertificateTree.check_eq_true_iff_valid {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (C : (Fin m → Sign) → Fin k → Fin n → ℤ)
    (p : Context m) (tree : IntegerCertificateTree m k) :
    tree.check A C p = true ↔ tree.Valid A C p := by
  induction tree generalizing p with
  | solved d w => simp only [IntegerCertificateTree.check, IntegerCertificateTree.Valid,
      Bool.and_eq_true, completeCheck_eq_true, finAll_eq_true, integerZeroSpanCheck_eq_true]
  | impossible w => simp only [IntegerCertificateTree.check, IntegerCertificateTree.Valid, integerFarkasCheck_eq_true]
  | split j neg zero pos ihn ihz ihp =>
    simp only [IntegerCertificateTree.check, IntegerCertificateTree.Valid, Bool.and_eq_true, ihn, ihz, ihp]

theorem IntegerCertificateTree.rational_valid {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (C : (Fin m → Sign) → Fin k → Fin n → ℤ)
    (p : Context m) (tree : IntegerCertificateTree m k) (ht : tree.Valid A C p) :
    tree.rational.Valid (integerForms A) (fun s t i => (C s t i : ℚ)) p := by
  induction tree generalizing p with
  | solved d w =>
    exact ⟨ht.1, fun t => rational_zeroSpan_of_integer A p (C (contextSigns p) t) (d t) (w t) (ht.2 t)⟩
  | impossible w => exact rational_farkas_of_integer A p w ht
  | split j neg zero pos ihn ihz ihp =>
    exact ⟨ihn _ ht.1, ihz _ ht.2.1, ihp _ ht.2.2⟩

theorem IntegerCertificateTree.all_real_of_valid {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (C : (Fin m → Sign) → Fin k → Fin n → ℤ)
    (tree : IntegerCertificateTree m k) (ht : tree.Valid A C (emptyContext m)) :
    ∀ x : Fin n → ℝ, ∀ t,
      evalForm (fun i => (C (actualSigns (integerForms A) x) t i : ℚ)) x = 0 :=
  tree.rational.all_real_of_valid (integerForms A) (fun s t i => (C s t i : ℚ))
    (tree.rational_valid A C (emptyContext m) ht)

theorem IntegerCertificateTree.all_real_of_check {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (C : (Fin m → Sign) → Fin k → Fin n → ℤ)
    (tree : IntegerCertificateTree m k) (ht : tree.check A C (emptyContext m) = true) :
    ∀ x : Fin n → ℝ, ∀ t,
      evalForm (fun i => (C (actualSigns (integerForms A) x) t i : ℚ)) x = 0 :=
  tree.all_real_of_valid A C ((tree.check_eq_true_iff_valid A C (emptyContext m)).mp ht)

def IntegerCertificateTree.Agrees {m n k : ℕ}
    (C D : (Fin m → Sign) → Fin k → Fin n → ℤ) (p : Context m) :
    IntegerCertificateTree m k → Prop
  | .solved _ _ => C (contextSigns p) = D (contextSigns p)
  | .impossible _ => True
  | .split j neg zero pos =>
      neg.Agrees C D (Function.update p j (some .neg)) ∧
      zero.Agrees C D (Function.update p j (some .zero)) ∧
      pos.Agrees C D (Function.update p j (some .pos))

theorem IntegerCertificateTree.valid_congr {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (C D : (Fin m → Sign) → Fin k → Fin n → ℤ)
    (p : Context m) (tree : IntegerCertificateTree m k)
    (ht : tree.Valid A C p) (ha : tree.Agrees C D p) : tree.Valid A D p := by
  induction tree generalizing p with
  | solved d w =>
    refine ⟨ht.1, ?_⟩
    change C (contextSigns p) = D (contextSigns p) at ha
    rw [← ha]
    exact ht.2
  | impossible w => exact ht
  | split j neg zero pos ihn ihz ihp =>
    exact ⟨ihn _ ht.1 ha.1, ihz _ ht.2.1 ha.2.1, ihp _ ht.2.2 ha.2.2⟩

end MaxCaterpillar.Frontier.StarCertificate
