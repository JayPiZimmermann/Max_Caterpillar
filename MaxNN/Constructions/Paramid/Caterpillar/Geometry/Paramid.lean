import MaxNN.Constructions.Paramid.Caterpillar.Geometry.BaseGerm
import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing
import MaxNN.Constructions.Paramid.Geom.Boundary.Facet

/-! # Caterpillar units as translated paramid units

The base has the direct expression
`w(lastHead S) + sum_j relu (w(parent S j) - w(j))`.
This identifies the actual caterpillar maximum with a linear term plus one
paramid unit. With distinct edge vectors, the existing two-crossing facet
theorem then applies. Distinctness is an explicit hypothesis of that bridge;
it is not assumed in the evaluation identity.
-/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m r : ℕ}

private theorem max_sub_eq_relu (a b : ℝ) : max a b - b = relu (a - b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, sub_self, relu_of_nonpos (sub_nonpos.mpr h)]
  · rw [max_eq_left h, relu_of_nonneg (sub_nonneg.mpr h)]

theorem baseMax_eq_last_add_sum_relu (w : Fin (r + 1) → ℝ)
    (S : Finset (Fin (r + 1))) :
    baseMax w S = w (lastHead S) +
      ∑ j : Fin r, relu (w (parent S j.succ) - w j.succ) := by
  rw [baseMax_eq_sum_parent_diff]
  simp_rw [max_sub_eq_relu]
  exact add_comm _ _

/-- The oriented edge from each child back to its parent. -/
def edgeVecs (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) :
    Fin r → Fin m → ℝ := fun j => A (parent S j.succ) - A j.succ

private theorem dot_sub_left (a b y : Fin m → ℝ) : dot (a - b) y = dot a y - dot b y := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem caterpillarUnit_eq_dot_add_paramidUnit (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) :
    caterpillarUnit apex A S = dot apex + paramidUnit (A (lastHead S) - apex) (edgeVecs A S) := by
  funext y
  change max (dot apex y) (baseMax (values A y) S) =
    dot apex y + relu (dot (A (lastHead S) - apex) y +
      ∑ j : Fin r, relu (dot (edgeVecs A S j) y))
  rw [baseMax_eq_last_add_sum_relu]
  simp only [edgeVecs, dot_sub_left, values]
  have he : dot (A (lastHead S)) y - dot apex y +
      (∑ j : Fin r, relu (dot (A (parent S j.succ)) y - dot (A j.succ) y)) =
      (dot (A (lastHead S)) y +
        ∑ j : Fin r, relu (dot (A (parent S j.succ)) y - dot (A j.succ) y)) - dot apex y := by
    ring
  rw [he, ← max_sub_eq_relu]
  rw [max_comm]
  ring

theorem caterpillarUnit_eq_dot_add_paramidOn (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1)))
    (hinj : Function.Injective (edgeVecs A S)) :
    caterpillarUnit apex A S = dot apex +
      paramidOn (A (lastHead S) - apex) (Finset.univ.image (edgeVecs A S)) := by
  rw [caterpillarUnit_eq_dot_add_paramidUnit, paramidUnit_eq_paramidOn _ _ hinj]

theorem germDiff_caterpillarUnit_eq_paramidOn (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1)))
    (hinj : Function.Injective (edgeVecs A S)) (u : Fin m → ℝ) :
    germDiff u (caterpillarUnit apex A S) =
      germDiff u (paramidOn (A (lastHead S) - apex) (Finset.univ.image (edgeVecs A S))) := by
  rw [caterpillarUnit_eq_dot_add_paramidOn apex A S hinj,
    germDiff_add (LSpan_le_SSpan m 1 (UnitGermAux.dot_mem_LSpan apex 1))
      (paramidOn_mem_SSpan _ _), germDiff_dot, zero_add]

/-- Two distinct crossing edges leave at most `r - 1` dimensions in the
two-sided germ. The unit itself is the original max-of-pair-max function. -/
theorem germDiff_caterpillarUnit_mem_LSpan_of_two (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1)))
    (hinj : Function.Injective (edgeVecs A S)) (u : Fin m → ℝ)
    (j k : Fin r) (hjk : j ≠ k)
    (hj : dot (A (parent S j.succ)) u ≠ dot (A j.succ) u)
    (hk : dot (A (parent S k.succ)) u ≠ dot (A k.succ) u) :
    germDiff u (caterpillarUnit apex A S) ∈ LSpan m (r - 1) := by
  classical
  rw [germDiff_caterpillarUnit_eq_paramidOn apex A S hinj u]
  apply germDiff_paramidOn_mem_LSpan_of_two
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    (fun he => hjk (hinj he))
  · simpa only [edgeVecs, dot_sub_left, sub_ne_zero] using hj
  · simpa only [edgeVecs, dot_sub_left, sub_ne_zero] using hk
  · have hc : (Finset.univ.image (edgeVecs A S)).card ≤ r := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_image_le (s := Finset.univ) (f := edgeVecs A S)
    have hr : 1 ≤ r := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le j.val) j.isLt)
    exact hc.trans (by rw [Nat.sub_add_cancel hr])

end MaxNN.Caterpillar
