import MaxNN.Constructions.Paramid.Caterpillar.Formula.Simplex
import MaxNN.Constructions.Paramid.Geom.Germ.Reflection

/-! # Global braid-direction cancellation for the explicit candidate

This DFS branch closes the braid mechanism for the actual finite candidate.
It proves the reduced vertex transposition is the required reflection, proves
the dual normalization, and derives a linear two-sided germ from the candidate's
proved permutation law. No reflection symmetry is left as a hypothesis.

The coordinate recurrence, noncoordinate block sum, and global MAX identity
are not asserted by this module.
-/

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {r : ℕ}

def braidValue (a b c : Fin (r + 1 + 1)) : ℝ :=
  (if c = a then 1 else 0) - (if c = b then 1 else 0)

/-- The full values `+1` at `a`, `-1` at `b`, and zero elsewhere, expressed
in reduced coordinates by subtracting the value at vertex zero. -/
def braidDirection (a b : Fin (r + 1 + 1)) : Fin (r + 1) → ℝ :=
  fun i => braidValue a b i.succ - braidValue a b 0

noncomputable def braidDual (a b : Fin (r + 1 + 1)) : Fin (r + 1) → ℝ :=
  (1 / 2 : ℝ) • (toR (vtx a) - toR (vtx b))

theorem simplexValues_braidDirection (a b c : Fin (r + 1 + 1)) :
    simplexValues (braidDirection a b) c = braidValue a b c - braidValue a b 0 := by
  refine Fin.cases ?_ (fun i => ?_) c
  · rw [simplexValues_zero, sub_self]
  · rw [simplexValues_succ]
    rfl

theorem dot_braidDual (a b : Fin (r + 1 + 1)) (y : Fin (r + 1) → ℝ) :
    dot (braidDual a b) y = (1 / 2 : ℝ) * (simplexValues y a - simplexValues y b) := by
  rw [braidDual, SupportCut.dot_smul_left, SupportCut.dot_sub_left]
  rfl

theorem dot_braidDual_direction (a b : Fin (r + 1 + 1)) (hab : a ≠ b) :
    dot (braidDual a b) (braidDirection a b) = 1 := by
  rw [dot_braidDual, simplexValues_braidDirection, simplexValues_braidDirection]
  simp only [braidValue, if_pos rfl, if_neg hab, if_neg (Ne.symm hab), ite_true]
  ring

private theorem values_swap (x : Fin (r + 1 + 1) → ℝ)
    (a b : Fin (r + 1 + 1)) (hab : a ≠ b) (c : Fin (r + 1 + 1)) :
    x (Equiv.swap a b c) = x c - (x a - x b) * braidValue a b c := by
  by_cases hca : c = a
  · subst c
    rw [Equiv.swap_apply_left]
    simp only [braidValue, if_pos rfl, if_neg hab, ite_true]
    ring
  · by_cases hcb : c = b
    · subst c
      rw [Equiv.swap_apply_right]
      simp only [braidValue, if_pos rfl, if_neg (Ne.symm hab), ite_true]
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
      simp only [braidValue, if_neg hca, if_neg hcb, sub_self, mul_zero, sub_zero]

theorem reflectAlong_braid_eq_permutedInput (a b : Fin (r + 1 + 1)) (hab : a ≠ b)
    (y : Fin (r + 1) → ℝ) :
    reflectAlong (braidDirection a b) (braidDual a b) y = permutedInput (Equiv.swap a b) y := by
  rw [reflectAlong_apply]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [dot_braidDual]
  change y i - (2 * ((1 / 2 : ℝ) * (simplexValues y a - simplexValues y b))) *
      (braidValue a b i.succ - braidValue a b 0) =
    simplexValues y (Equiv.swap a b i.succ) - simplexValues y (Equiv.swap a b 0)
  rw [values_swap (simplexValues y) a b hab i.succ,
    values_swap (simplexValues y) a b hab 0, simplexValues_succ, simplexValues_zero]
  ring

/-- The actual factorial-weighted sum has a linear facet datum in every
canonical braid direction, including swaps involving the zero vertex. -/
theorem germDiff_formula_braid_mem_LSpan_zero (a b : Fin (r + 1 + 1)) (hab : a ≠ b) :
    germDiff (braidDirection a b) (formula r) ∈ LSpan (r + 1) 0 := by
  apply germDiff_mem_LSpan_zero_of_reflection_add_linear (formula_mem_SSpan r)
    (braidDirection a b) (braidDual a b)
    ((-totalWeight r) • toR (vtx (Equiv.swap a b 0))) (dot_braidDual_direction a b hab)
  intro y
  rw [reflectAlong_braid_eq_permutedInput a b hab, formula_permutedInput,
    SupportCut.dot_smul_left]
  change formula r y - totalWeight r * simplexValues y (Equiv.swap a b 0) =
    formula r y + (-totalWeight r) * simplexValues y (Equiv.swap a b 0)
  ring

/-- All scalar multiples are included, with the zero direction giving zero
facet datum. A negative scalar reverses the sign, which preserves the span. -/
theorem germDiff_formula_smul_braid_mem_LSpan_zero
    (a b : Fin (r + 1 + 1)) (hab : a ≠ b) (t : ℝ) :
    germDiff (t • braidDirection a b) (formula r) ∈ LSpan (r + 1) 0 := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have he : t • braidDirection a b = (-t) • (-braidDirection a b) := by
      simp only [smul_neg, neg_smul, neg_neg]
    rw [he, germDiff_pos_smul (formula_mem_SSpan r) (neg_pos.mpr ht)]
    have hn := Submodule.neg_mem (LSpan (r + 1) 0)
      (germDiff_formula_braid_mem_LSpan_zero a b hab)
    simpa only [germDiff_eq_sub, neg_neg, neg_sub] using hn
  · subst t
    rw [zero_smul, germDiff_eq_sub, neg_zero, sub_self]
    exact Submodule.zero_mem _
  · rw [germDiff_pos_smul (formula_mem_SSpan r) ht]
    exact germDiff_formula_braid_mem_LSpan_zero a b hab

end MaxNN.Caterpillar
