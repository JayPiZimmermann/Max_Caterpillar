import MaxCaterpillar.Frontier.StarCertificate.Checker.Farkas

/-! # A complete ternary-tree checker over all real inputs

Each split follows the actual sign of one rational linear form. An
infeasible prefix is rejected only by a checked Farkas identity; every
remaining leaf checks every target coefficient modulo the zero-form span.
Thus no independently assumed face-list completeness enters soundness.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

inductive CertificateTree (m k : ℕ) where
  | solved (multipliers : Fin k → Fin m → ℚ)
  | impossible (weights : Fin m → ℚ)
  | split (j : Fin m) (neg zero pos : CertificateTree m k)

def CertificateTree.Valid {m n k : ℕ} (A : Fin m → RationalForm n)
    (C : (Fin m → Sign) → Fin k → RationalForm n) (p : Context m) :
    CertificateTree m k → Prop
  | .solved w => Complete p ∧ ∀ t, ZeroSpanValid A p (C (contextSigns p) t) (w t)
  | .impossible w => FarkasValid A p w
  | .split j neg zero pos =>
      neg.Valid A C (Function.update p j (some .neg)) ∧
      zero.Valid A C (Function.update p j (some .zero)) ∧
      pos.Valid A C (Function.update p j (some .pos))

def CertificateTree.check {m n k : ℕ} (A : Fin m → RationalForm n)
    (C : (Fin m → Sign) → Fin k → RationalForm n) (p : Context m) :
    CertificateTree m k → Bool
  | .solved w => decide (Complete p ∧ ∀ t, ZeroSpanValid A p (C (contextSigns p) t) (w t))
  | .impossible w => decide (FarkasValid A p w)
  | .split j neg zero pos =>
      neg.check A C (Function.update p j (some .neg)) &&
      (zero.check A C (Function.update p j (some .zero)) &&
      pos.check A C (Function.update p j (some .pos)))

theorem CertificateTree.check_eq_true_iff_valid {m n k : ℕ}
    (A : Fin m → RationalForm n) (C : (Fin m → Sign) → Fin k → RationalForm n)
    (p : Context m) (tree : CertificateTree m k) :
    tree.check A C p = true ↔ tree.Valid A C p := by
  induction tree generalizing p with
  | solved w => simp only [CertificateTree.check, CertificateTree.Valid, decide_eq_true_eq]
  | impossible w => simp only [CertificateTree.check, CertificateTree.Valid, decide_eq_true_eq]
  | split j neg zero pos ihn ihz ihp =>
    simp only [CertificateTree.check, CertificateTree.Valid, Bool.and_eq_true, ihn, ihz, ihp]

/-- The semantic coverage theorem follows a real vector through each
ternary split; all equality branches are included explicitly. -/
theorem CertificateTree.valid_sound {m n k : ℕ}
    (A : Fin m → RationalForm n) (C : (Fin m → Sign) → Fin k → RationalForm n)
    (p : Context m) (tree : CertificateTree m k) (ht : tree.Valid A C p)
    (x : Fin n → ℝ) (hp : Holds A p x) :
    ∀ t, evalForm (C (actualSigns A x) t) x = 0 := by
  induction tree generalizing p with
  | solved w =>
    have hsigns := complete_signs_eq_actual A p x ht.1 hp
    intro t
    rw [← hsigns]
    exact zeroSpan_vanishes A p (C (contextSigns p) t) (w t) (ht.2 t) x hp
  | impossible w => exact False.elim (farkas_impossible A p w ht x hp)
  | split j neg zero pos ihn ihz ihp =>
    rcases lt_trichotomy (evalForm (A j) x) 0 with hn | hz | hpos
    · exact ihn (Function.update p j (some .neg)) ht.1
        (holds_update A p x hp j .neg hn)
    · exact ihz (Function.update p j (some .zero)) ht.2.1
        (holds_update A p x hp j .zero hz)
    · exact ihp (Function.update p j (some .pos)) ht.2.2
        (holds_update A p x hp j .pos hpos)

/-- A finite rational check certifies every target identity on all real
inputs. Feasible sign patterns need not be listed or assumed exhaustive. -/
theorem CertificateTree.all_real_of_check {m n k : ℕ}
    (A : Fin m → RationalForm n) (C : (Fin m → Sign) → Fin k → RationalForm n)
    (tree : CertificateTree m k) (ht : tree.check A C (emptyContext m) = true) :
    ∀ x : Fin n → ℝ, ∀ t, evalForm (C (actualSigns A x) t) x = 0 := by
  intro x
  exact tree.valid_sound A C (emptyContext m)
    ((tree.check_eq_true_iff_valid A C (emptyContext m)).mp ht) x (holds_empty A x)

theorem CertificateTree.all_real_of_valid {m n k : ℕ}
    (A : Fin m → RationalForm n) (C : (Fin m → Sign) → Fin k → RationalForm n)
    (tree : CertificateTree m k) (ht : tree.Valid A C (emptyContext m)) :
    ∀ x : Fin n → ℝ, ∀ t, evalForm (C (actualSigns A x) t) x = 0 := by
  intro x
  exact tree.valid_sound A C (emptyContext m) ht x (holds_empty A x)

/-- Only solved-leaf coefficient values matter when transporting a tree
certificate to an independently defined symbolic target. -/
def CertificateTree.Agrees {m n k : ℕ}
    (C D : (Fin m → Sign) → Fin k → RationalForm n) (p : Context m) :
    CertificateTree m k → Prop
  | .solved _ => C (contextSigns p) = D (contextSigns p)
  | .impossible _ => True
  | .split j neg zero pos =>
      neg.Agrees C D (Function.update p j (some .neg)) ∧
      zero.Agrees C D (Function.update p j (some .zero)) ∧
      pos.Agrees C D (Function.update p j (some .pos))

theorem CertificateTree.valid_congr {m n k : ℕ}
    (A : Fin m → RationalForm n) (C D : (Fin m → Sign) → Fin k → RationalForm n)
    (p : Context m) (tree : CertificateTree m k)
    (ht : tree.Valid A C p) (ha : tree.Agrees C D p) : tree.Valid A D p := by
  induction tree generalizing p with
  | solved w =>
    refine ⟨ht.1, ?_⟩
    change C (contextSigns p) = D (contextSigns p) at ha
    rw [← ha]
    exact ht.2
  | impossible w => exact ht
  | split j neg zero pos ihn ihz ihp =>
    exact ⟨ihn _ ht.1 ha.1, ihz _ ht.2.1 ha.2.1, ihp _ ht.2.2 ha.2.2⟩

/-- An independently proved symbolic linearization bridge connects the
generic checker to the actual expression of interest. -/
theorem CertificateTree.identities_of_check {m n k : ℕ}
    (A : Fin m → RationalForm n) (C : (Fin m → Sign) → Fin k → RationalForm n)
    (F : (Fin n → ℝ) → Fin k → ℝ)
    (hF : ∀ x t, F x t = evalForm (C (actualSigns A x) t) x)
    (tree : CertificateTree m k) (ht : tree.check A C (emptyContext m) = true) :
    ∀ x t, F x t = 0 := by
  intro x t
  rw [hF x t]
  exact tree.all_real_of_check A C ht x t

end MaxCaterpillar.Frontier.StarCertificate
