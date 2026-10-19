import MaxNN.Constructions.Paramid.Caterpillar.Formula.Braid

/-! # Only block directions remain for the full candidate

The unit-level value classification is transported to the entire simplex.
The complete candidate, including its actual coefficients, has a lower-order
facet datum in every direction whose full vertex values do not take at most
two values. This closes the braid and all other non-block branches; it does
not assert cancellation in the noncoordinate block directions.
-/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {r : ℕ}

/-- The full simplex vertex values have at most two levels. -/
def BlockDirection (u : Fin (r + 1) → ℝ) : Prop :=
  ∃ c d : ℝ, ∀ a : Fin (r + 1 + 1), simplexValues u a = c ∨ simplexValues u a = d

/-- A scalar multiple of the reduced direction of a vertex transposition. -/
def BraidDirection (u : Fin (r + 1) → ℝ) : Prop :=
  ∃ a b : Fin (r + 1 + 1), a ≠ b ∧ ∃ t : ℝ, u = t • braidDirection a b

theorem blockDirection_of_word (π : Equiv.Perm (Fin (r + 1 + 1)))
    (u : Fin (r + 1) → ℝ)
    (h : BlockValues (toR (vtx (π 0))) (fun i => toR (vtx (π i.succ))) u) :
    BlockDirection u := by
  obtain ⟨c, hc⟩ := h
  refine ⟨simplexValues u (π 0), c, ?_⟩
  intro a
  obtain ⟨k, rfl⟩ := π.surjective a
  refine Fin.cases ?_ (fun i => ?_) k
  · exact Or.inl rfl
  · exact hc i

theorem eq_smul_braidDirection_of_values (u : Fin (r + 1) → ℝ)
    (a b : Fin (r + 1 + 1)) (hab : a ≠ b) (c : ℝ)
    (hother : ∀ q, q ≠ a → q ≠ b → simplexValues u q = c)
    (hsum : simplexValues u a + simplexValues u b = 2 * c) :
    u = (simplexValues u a - c) • braidDirection a b := by
  have hx : ∀ q, simplexValues u q =
      c + (simplexValues u a - c) * braidValue a b q := by
    intro q
    by_cases hqa : q = a
    · subst q
      simp only [braidValue, if_pos rfl, if_neg hab, ite_true]
      ring
    · by_cases hqb : q = b
      · subst q
        simp only [braidValue, if_pos rfl, if_neg (Ne.symm hab), ite_true]
        linarith
      · rw [hother q hqa hqb]
        simp only [braidValue, if_neg hqa, if_neg hqb, sub_self, mul_zero, add_zero]
  have hzero := hx 0
  rw [simplexValues_zero] at hzero
  funext i
  have hi := hx i.succ
  rw [simplexValues_succ] at hi
  change u i = (simplexValues u a - c) * (braidValue a b i.succ - braidValue a b 0)
  nlinarith only [hi, hzero]

theorem braidDirection_of_word (π : Equiv.Perm (Fin (r + 1 + 1)))
    (u : Fin (r + 1) → ℝ)
    (h : BraidValues (toR (vtx (π 0))) (fun i => toR (vtx (π i.succ))) u) :
    BraidDirection u := by
  obtain ⟨j, c, hc, hsum⟩ := h
  have hab : π 0 ≠ π j.succ.succ := fun he => Fin.succ_ne_zero _ (π.injective he).symm
  refine ⟨π 0, π j.succ.succ, hab, simplexValues u (π 0) - c, ?_⟩
  apply eq_smul_braidDirection_of_values u _ _ hab c _ hsum
  intro q hqa hqb
  obtain ⟨k, rfl⟩ := π.surjective q
  have hfull : ∀ k : Fin (r + 1 + 1),
      π k ≠ π 0 → π k ≠ π j.succ.succ → simplexValues u (π k) = c := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · intro hne
      exact False.elim (hne rfl)
    · intro _ hne
      apply hc i
      intro hi
      exact hne (congrArg π (congrArg Fin.succ hi))
  exact hfull k hqa hqb

theorem germDiff_formula_mem_LSpan_zero_of_braidDirection
    (u : Fin (r + 1) → ℝ) (h : BraidDirection u) :
    germDiff u (formula r) ∈ LSpan (r + 1) 0 := by
  obtain ⟨a, b, hab, t, rfl⟩ := h
  exact germDiff_formula_smul_braid_mem_LSpan_zero a b hab t

/-- Global facet classification for the complete candidate. For `N = r+2`
vertices, every non-block direction has facet datum of dimension at most
`N-3`, so only the block family can contribute to the top facet class. -/
theorem germDiff_formula_mem_LSpan_of_not_blockDirection (hr : 2 ≤ r)
    (u : Fin (r + 1) → ℝ) (hblock : ¬ BlockDirection u) :
    germDiff u (formula r) ∈ LSpan (r + 1) (r - 1) := by
  classical
  by_cases hbraid : BraidDirection u
  · exact DoublingAux.LSpan_mono (Nat.zero_le _)
      (germDiff_formula_mem_LSpan_zero_of_braidDirection u hbraid)
  · rw [germDiff_formula_eq_sum]
    apply Submodule.sum_mem
    intro π _
    apply Submodule.sum_mem
    intro S _
    apply Submodule.smul_mem
    apply germDiff_permutationWord_mem_LSpan_of_no_patterns hr π S u
    · intro h
      exact hblock (blockDirection_of_word π u h)
    · intro h
      exact hbraid (braidDirection_of_word π u h)

end MaxNN.Caterpillar
