import MaxNN.Constructions.Paramid.Caterpillar.Formula.Simplex
import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing.Base

/-! # Coordinate germs of one caterpillar word

The coordinate normal has value zero at one distinguished simplex vertex and
value one at every other vertex.  If the distinguished vertex is in the base
word and there is only one crossing tree edge, the edge is either a pendant
edge or a spine cut.  The two lemmas below compute the complete two-sided germ
in those cases.  They retain the lower-dimensional base-germ summand instead
of silently passing to facet classes.
-/

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m r : ℕ}

/-- The reduced coordinate normal for the simplex facet opposite vertex zero. -/
def zeroCoordinateDirection (m : ℕ) : Fin m → ℝ := fun _ => 1

theorem simplexValues_zeroCoordinateDirection_zero :
    simplexValues (zeroCoordinateDirection (r + 1)) (0 : Fin (r + 1 + 1)) = 0 := by
  rw [simplexValues_zero]

theorem simplexValues_zeroCoordinateDirection_succ (i : Fin (r + 1)) :
    simplexValues (zeroCoordinateDirection (r + 1)) i.succ = 1 := by
  rw [simplexValues_succ]
  rfl

/-- A unique pendant crossing contributes the negative of its tied face,
up to the explicitly displayed one-dimensional base germ. -/
theorem germDiff_caterpillarUnit_coordinate_pendant
    (apex : Fin m → ℝ) (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r) (hj : j.succ ∉ S)
    (u : Fin m → ℝ) (ha : dot apex u = 1) (hAj : dot (A j.succ) u = 0)
    (hA : ∀ i : Fin (r + 1), i ≠ j.succ → dot (A i) u = 1) :
    germDiff u (caterpillarUnit apex A S) = fun y =>
      baseGerm A S u y - max (dot apex y) (baseGerm A S (-u) y) := by
  have hbase : baseMax (values A u) S = 2 := by
    rw [baseMax_single_pendant (values A u) S j hj 1 hA]
    change max (1 : ℝ) (dot (A j.succ) u) + 1 - dot (A j.succ) u = 2
    rw [hAj]
    norm_num
  have hbaseNeg : baseMax (values A (-u)) S = -1 := by
    have hAneg : ∀ i : Fin (r + 1), i ≠ j.succ → values A (-u) i = -1 := by
      intro i hi
      change dot (A i) (-u) = -1
      rw [UnitGermAux.dot_neg_right, hA i hi]
    rw [baseMax_single_pendant (values A (-u)) S j hj (-1) hAneg]
    change max (-1 : ℝ) (dot (A j.succ) (-u)) + (-1) - dot (A j.succ) (-u) = -1
    rw [UnitGermAux.dot_neg_right, hAj]
    norm_num
  have hp := isGerm_max_of_lt (isGerm_dot apex u) (isGerm_baseMax A S u) (by
    rw [ha, hbase]
    norm_num)
  have hn := isGerm_max_of_eq (isGerm_dot apex (-u)) (isGerm_baseMax A S (-u)) (by
    rw [UnitGermAux.dot_neg_right, ha, hbaseNeg])
  funext y
  unfold germDiff
  change germ (fun z => max (dot apex z) (baseMax (values A z) S)) u y -
    germ (fun z => max (dot apex z) (baseMax (values A z) S)) (-u) y = _
  rw [germ_eq_of_isGerm hp, germ_eq_of_isGerm hn]

theorem germDiff_add_coordinatePendantFace_mem_LSpan_one
    (apex : Fin m → ℝ) (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r) (hj : j.succ ∉ S)
    (u : Fin m → ℝ) (ha : dot apex u = 1) (hAj : dot (A j.succ) u = 0)
    (hA : ∀ i : Fin (r + 1), i ≠ j.succ → dot (A i) u = 1) :
    germDiff u (caterpillarUnit apex A S) +
      (fun y => max (dot apex y) (baseGerm A S (-u) y)) ∈ LSpan m 1 := by
  rw [germDiff_caterpillarUnit_coordinate_pendant apex A S j hj u ha hAj hA]
  have he : (fun y => baseGerm A S u y - max (dot apex y) (baseGerm A S (-u) y)) +
      (fun y => max (dot apex y) (baseGerm A S (-u) y)) = baseGerm A S u := by
    funext y
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact baseGerm_mem_LSpan_one A S u

/-- A unique spine crossing contributes its tied face, up to the explicitly
displayed one-dimensional opposite base germ. -/
theorem germDiff_caterpillarUnit_coordinate_cut
    (apex : Fin m → ℝ) (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r) (hj : j.succ ∈ S)
    (u : Fin m → ℝ) (ha : dot apex u = 1)
    (hroot : dot (A 0) u = 1) (hAj : dot (A j.succ) u = 0)
    (hother : ∀ k : Fin r, k ≠ j →
      dot (A k.succ) u = dot (A (parent S k.succ)) u) :
    germDiff u (caterpillarUnit apex A S) = fun y =>
      max (dot apex y) (baseGerm A S u y) - baseGerm A S (-u) y := by
  have hbase : baseMax (values A u) S = 1 := by
    rw [baseMax_unique_cut S (values A u) j hj hother]
    change max (dot (A 0) u) (dot (A j.succ) u) = 1
    rw [hroot, hAj]
    norm_num
  have hotherNeg : ∀ k : Fin r, k ≠ j →
      dot (A k.succ) (-u) = dot (A (parent S k.succ)) (-u) := by
    intro k hk
    rw [UnitGermAux.dot_neg_right, UnitGermAux.dot_neg_right, hother k hk]
  have hbaseNeg : baseMax (values A (-u)) S = 0 := by
    rw [baseMax_unique_cut S (values A (-u)) j hj hotherNeg]
    change max (dot (A 0) (-u)) (dot (A j.succ) (-u)) = 0
    rw [UnitGermAux.dot_neg_right, UnitGermAux.dot_neg_right, hroot, hAj]
    norm_num
  have hp := isGerm_max_of_eq (isGerm_dot apex u) (isGerm_baseMax A S u) (by
    rw [ha, hbase])
  have hn := isGerm_max_of_lt (isGerm_dot apex (-u)) (isGerm_baseMax A S (-u)) (by
    rw [UnitGermAux.dot_neg_right, ha, hbaseNeg]
    norm_num)
  funext y
  unfold germDiff
  change germ (fun z => max (dot apex z) (baseMax (values A z) S)) u y -
    germ (fun z => max (dot apex z) (baseMax (values A z) S)) (-u) y = _
  rw [germ_eq_of_isGerm hp, germ_eq_of_isGerm hn]

theorem germDiff_sub_coordinateCutFace_mem_LSpan_one
    (apex : Fin m → ℝ) (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r) (hj : j.succ ∈ S)
    (u : Fin m → ℝ) (ha : dot apex u = 1)
    (hroot : dot (A 0) u = 1) (hAj : dot (A j.succ) u = 0)
    (hother : ∀ k : Fin r, k ≠ j →
      dot (A k.succ) u = dot (A (parent S k.succ)) u) :
    germDiff u (caterpillarUnit apex A S) -
      (fun y => max (dot apex y) (baseGerm A S u y)) ∈ LSpan m 1 := by
  rw [germDiff_caterpillarUnit_coordinate_cut apex A S j hj u ha hroot hAj hother]
  have he : (fun y => max (dot apex y) (baseGerm A S u y) - baseGerm A S (-u) y) -
      (fun y => max (dot apex y) (baseGerm A S u y)) = -baseGerm A S (-u) := by
    funext y
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  rw [he]
  exact Submodule.neg_mem _ (baseGerm_mem_LSpan_one A S (-u))

end MaxNN.Caterpillar
