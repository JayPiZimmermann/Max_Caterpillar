import MaxCaterpillar.Frontier.StarCertificate.Checker.Even

/-! # Region-wise real identities over the same checked tree

This layer is for proved symmetry reductions of the actual real target.
It does not require equality of coefficient vectors on degenerate faces.
Every solved-leaf identity must be supplied by a proved representative
certificate and a proved transport; impossible leaves retain exact Farkas
certificates. The tree traversal itself still covers every real vector.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate

theorem holds_some_of_actual_signs {m n : ℕ} (A : Fin m → RationalForm n)
    (pattern : Fin m → Sign) (x : Fin n → ℝ) (hs : actualSigns A x = pattern) :
    Holds A (fun j => some (pattern j)) x := by
  intro j s hj
  have hjs : pattern j = s := Option.some.inj hj
  subst s
  have he := congr_fun hs j
  change signOf (evalForm (A j) x) = pattern j at he
  rw [← he]
  exact signOf_holds _

/-- One checked integer representative proves the real target identity on
its entire sign stratum, not merely at an interior witness. -/
theorem integer_representative_sound {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (C : (Fin m → Sign) → Fin k → Fin n → ℤ)
    (pattern : Fin m → Sign) (a : Fin k → Fin n → ℤ)
    (den : Fin k → ℤ) (w : Fin k → Fin m → ℤ)
    (hspan : ∀ t, IntegerZeroSpanValid A (fun j => some (pattern j)) (a t) (den t) (w t))
    (hmatch : C pattern = a) (x : Fin n → ℝ)
    (hx : actualSigns (integerForms A) x = pattern) :
    ∀ t, evalForm (fun i => (C (actualSigns (integerForms A) x) t i : ℚ)) x = 0 := by
  intro t
  rw [hx, hmatch]
  exact zeroSpan_vanishes (integerForms A) (fun j => some (pattern j))
    (fun i => (a t i : ℚ)) (fun j => (w t j : ℚ) / (den t : ℚ))
    (rational_zeroSpan_of_integer A _ (a t) (den t) (w t) (hspan t)) x
    (holds_some_of_actual_signs (integerForms A) pattern x hx)

def IntegerCertificateTree.FunctionalValid {m n k : ℕ} (A : Fin m → Fin n → ℤ)
    (F : (Fin n → ℝ) → Fin k → ℝ) (p : Context m) :
    IntegerCertificateTree m k → Prop
  | .solved _ _ => ∀ x, Holds (integerForms A) p x → ∀ t, F x t = 0
  | .impossible w => IntegerFarkasValid A p w
  | .split j neg zero pos =>
      neg.FunctionalValid A F (Function.update p j (some .neg)) ∧
      zero.FunctionalValid A F (Function.update p j (some .zero)) ∧
      pos.FunctionalValid A F (Function.update p j (some .pos))

def IntegerCertificateTree.GeometryValid {m n k : ℕ} (A : Fin m → Fin n → ℤ)
    (p : Context m) : IntegerCertificateTree m k → Prop
  | .solved _ _ => Complete p
  | .impossible w => IntegerFarkasValid A p w
  | .split j neg zero pos =>
      neg.GeometryValid A (Function.update p j (some .neg)) ∧
      zero.GeometryValid A (Function.update p j (some .zero)) ∧
      pos.GeometryValid A (Function.update p j (some .pos))

theorem IntegerCertificateTree.geometry_of_valid {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (C : (Fin m → Sign) → Fin k → Fin n → ℤ)
    (p : Context m) (tree : IntegerCertificateTree m k) (ht : tree.Valid A C p) :
    tree.GeometryValid A p := by
  induction tree generalizing p with
  | solved d w => exact ht.1
  | impossible w => exact ht
  | split j neg zero pos ihn ihz ihp => exact ⟨ihn _ ht.1, ihz _ ht.2.1, ihp _ ht.2.2⟩

def IntegerCertificateTree.solvedPatterns {m k : ℕ} (p : Context m) :
    IntegerCertificateTree m k → List (Fin m → Sign)
  | .solved _ _ => [contextSigns p]
  | .impossible _ => []
  | .split j neg zero pos =>
      neg.solvedPatterns (Function.update p j (some .neg)) ++
      (zero.solvedPatterns (Function.update p j (some .zero)) ++
      pos.solvedPatterns (Function.update p j (some .pos)))

/-- Checked geometry can be reused with any independently proved real
solver for each listed solved pattern. No coefficient equality is required. -/
theorem IntegerCertificateTree.functional_of_geometry {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (F : (Fin n → ℝ) → Fin k → ℝ)
    (p : Context m) (tree : IntegerCertificateTree m k) (ht : tree.GeometryValid A p)
    (hs : ∀ pattern, pattern ∈ tree.solvedPatterns p →
      ∀ x, actualSigns (integerForms A) x = pattern → ∀ t, F x t = 0) :
    tree.FunctionalValid A F p := by
  induction tree generalizing p with
  | solved d w =>
    intro x hx
    exact hs (contextSigns p) (by simp only [solvedPatterns, List.mem_singleton]) x
      (complete_signs_eq_actual (integerForms A) p x ht hx).symm
  | impossible w => exact ht
  | split j neg zero pos ihn ihz ihp =>
    refine ⟨ihn _ ht.1 ?_, ihz _ ht.2.1 ?_, ihp _ ht.2.2 ?_⟩
    · intro pattern hp
      exact hs pattern (List.mem_append.mpr (Or.inl hp))
    · intro pattern hp
      exact hs pattern (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hp))))
    · intro pattern hp
      exact hs pattern (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hp))))

theorem IntegerCertificateTree.functional_sound {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (F : (Fin n → ℝ) → Fin k → ℝ)
    (p : Context m) (tree : IntegerCertificateTree m k)
    (ht : tree.FunctionalValid A F p) (x : Fin n → ℝ)
    (hp : Holds (integerForms A) p x) : ∀ t, F x t = 0 := by
  induction tree generalizing p with
  | solved d w => exact ht x hp
  | impossible w =>
    exact False.elim (farkas_impossible (integerForms A) p (fun j => (w j : ℚ))
      (rational_farkas_of_integer A p w ht) x hp)
  | split j neg zero pos ihn ihz ihp =>
    rcases lt_trichotomy (evalForm ((integerForms A) j) x) 0 with hn | hz | hpos
    · exact ihn _ ht.1 (holds_update _ _ _ hp j .neg hn)
    · exact ihz _ ht.2.1 (holds_update _ _ _ hp j .zero hz)
    · exact ihp _ ht.2.2 (holds_update _ _ _ hp j .pos hpos)

theorem IntegerCertificateTree.all_real_of_functional_valid {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (F : (Fin n → ℝ) → Fin k → ℝ)
    (tree : IntegerCertificateTree m k)
    (ht : tree.FunctionalValid A F (emptyContext m)) : ∀ x t, F x t = 0 :=
  fun x => tree.functional_sound A F _ ht x (holds_empty _ _)

/-- Real symmetry transports can replace coefficient equality at solved
faces. The nonpositive and zero cases are traversed explicitly, then actual
evenness supplies the positive halfspace. -/
theorem functional_halfspace_even_sound {m n k : ℕ}
    (A : Fin m → Fin n → ℤ) (r : Fin m) (j : Fin n)
    (hcoordinate : ∀ x, evalForm ((integerForms A) r) x = x j)
    (F : (Fin n → ℝ) → Fin k → ℝ)
    (negative zero : IntegerCertificateTree m k)
    (hn : negative.FunctionalValid A F (Function.update (emptyContext m) r (some .neg)))
    (hz : zero.FunctionalValid A F (Function.update (emptyContext m) r (some .zero)))
    (heven : ∀ x t, F (-x) t = F x t) : ∀ x t, F x t = 0 := by
  intro x t
  refine even_zero_of_nonpositive_coordinate j (fun y => F y t) (fun y => heven y t)
    (fun y hy => ?_) x
  rcases lt_or_eq_of_le hy with hlt | heq
  · have hp : Holds (integerForms A) (Function.update (emptyContext m) r (some .neg)) y :=
      holds_update _ _ _ (holds_empty _ _) r .neg (by
        change evalForm ((integerForms A) r) y < 0
        rw [hcoordinate]
        exact hlt)
    exact negative.functional_sound A F _ hn y hp t
  · have hp : Holds (integerForms A) (Function.update (emptyContext m) r (some .zero)) y :=
      holds_update _ _ _ (holds_empty _ _) r .zero (by
        change evalForm ((integerForms A) r) y = 0
        rw [hcoordinate]
        exact heq)
    exact zero.functional_sound A F _ hz y hp t

end MaxCaterpillar.Frontier.StarCertificate
