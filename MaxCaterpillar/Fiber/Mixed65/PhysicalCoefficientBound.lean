import MaxCaterpillar.Fiber.Mixed65.BoundaryCoefficients
import MaxCaterpillar.Fiber.Mixed65.PhysicalMinimalExtraction

/-! # Comparison with the actual physical coefficient size

These inequalities concern the entries of the original weight matrices.
They introduce neither normalized gate coefficients nor a chosen residual
parameterization. The quantitative residual divergence theorem is a separate
input to the eventual normalized coefficient bound.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators

variable {m : ℕ}

theorem coefficientSize_nonneg (net : Network 4 6 m) : 0 ≤ coefficientSize net := by
  exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg _

/-- A single effective physical coefficient is bounded by the full physical
coefficient size, including all carrier columns. -/
theorem effectiveCoefficient_abs_le (net : Network 4 6 m) (k : Fin m) (j : Fin 6) :
    |net.w₃ k * net.W₂ k j| ≤ coefficientSize net := by
  exact (Finset.single_le_sum (fun i _ => abs_nonneg (net.w₃ k * net.W₂ k i))
    (Finset.mem_univ j)).trans
      (Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg fun a _ => abs_nonneg (net.w₃ i * net.W₂ i a))
        (Finset.mem_univ k))

/-- The total effective coefficient in one column, even on an arbitrary
selected subset of neurons, is bounded by the physical coefficient size. -/
theorem effectiveCoefficient_columnSum_le (net : Network 4 6 m)
    (S : Finset (Fin m)) (j : Fin 6) :
    (∑ k in S, |net.w₃ k * net.W₂ k j|) ≤ coefficientSize net := by
  calc
    (∑ k in S, |net.w₃ k * net.W₂ k j|) ≤
        ∑ k, |net.w₃ k * net.W₂ k j| := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun k _ _ => abs_nonneg _)
    _ ≤ coefficientSize net := by
      apply Finset.sum_le_sum
      intro k _
      exact Finset.single_le_sum
        (fun i _ => abs_nonneg (net.w₃ k * net.W₂ k i)) (Finset.mem_univ j)

/-- Recession leaves this size exactly unchanged, as it changes only biases. -/
@[simp] theorem coefficientSize_zeroBias (net : Network 4 6 m) :
    coefficientSize net.zeroBias = coefficientSize net := rfl

/-- A quantitative lower bound on any unchanged residual column transfers
directly to the physical norm. -/
theorem coefficientSize_bound_of_column (net : Network 4 6 m)
    (S : Finset (Fin m)) (j : Fin 6) (t : ℝ) (ht : 0 ≤ t)
    (h : 1 ≤ t * ∑ k in S, |net.w₃ k * net.W₂ k j|) :
    1 ≤ t * coefficientSize net :=
  h.trans (mul_le_mul_of_nonneg_left (effectiveCoefficient_columnSum_le net S j) ht)

theorem effectiveCoefficient_firstFour_le_row (net : Network 4 6 m) (k : Fin m) :
    |net.w₃ k * net.W₂ k 0| + |net.w₃ k * net.W₂ k 1| +
      |net.w₃ k * net.W₂ k 2| + |net.w₃ k * net.W₂ k 3| ≤
        ∑ j, |net.w₃ k * net.W₂ k j| := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({0, 1, 2, 3} : Finset (Fin 6)))
    (fun j _ _ => abs_nonneg (net.w₃ k * net.W₂ k j))
  rw [Finset.sum_insert (by decide : (0 : Fin 6) ∉ ({1, 2, 3} : Finset (Fin 6))),
    Finset.sum_insert (by decide : (1 : Fin 6) ∉ ({2, 3} : Finset (Fin 6))),
    Finset.sum_insert (by decide : (2 : Fin 6) ∉ ({3} : Finset (Fin 6))),
    Finset.sum_singleton] at h
  simpa only [add_assoc] using h

/-- The sum of all four effective invariant coefficients over the selected
physical gates is bounded by the actual six-column coefficient size. -/
theorem effectiveCoefficient_firstFourSum_le (net : Network 4 6 m)
    (S : Finset (Fin m)) :
    (∑ k in S, (|net.w₃ k * net.W₂ k 0| + |net.w₃ k * net.W₂ k 1| +
      |net.w₃ k * net.W₂ k 2| + |net.w₃ k * net.W₂ k 3|)) ≤
        coefficientSize net := by
  calc
    (∑ k in S, (|net.w₃ k * net.W₂ k 0| + |net.w₃ k * net.W₂ k 1| +
      |net.w₃ k * net.W₂ k 2| + |net.w₃ k * net.W₂ k 3|)) ≤
        ∑ k in S, ∑ j, |net.w₃ k * net.W₂ k j| :=
      Finset.sum_le_sum fun k _ => effectiveCoefficient_firstFour_le_row net k
    _ ≤ coefficientSize net :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun k _ _ => Finset.sum_nonneg fun j _ => abs_nonneg _)

/-- The abstract residual system's effective coefficient size is exactly a
subsum of the original physical entries, and hence is bounded by their size. -/
theorem physicalResidualSystem_effective_sum_le (net : Network 4 6 m)
    (S : Finset (Fin m)) (l : Fin m → ℝ) :
    (∑ k : S,
      (|(physicalResidualSystem net S l).out k * (physicalResidualSystem net S l).U k| +
      |(physicalResidualSystem net S l).out k * (physicalResidualSystem net S l).V k| +
      |(physicalResidualSystem net S l).out k * (physicalResidualSystem net S l).W k| +
      |(physicalResidualSystem net S l).out k * (physicalResidualSystem net S l).T k|)) ≤
        coefficientSize net := by
  change (∑ k : S, (|net.w₃ k.val * net.W₂ k.val 0| + |net.w₃ k.val * net.W₂ k.val 1| +
    |net.w₃ k.val * net.W₂ k.val 2| + |net.w₃ k.val * net.W₂ k.val 3|)) ≤ coefficientSize net
  rw [Finset.sum_coe_sort S (fun k => |net.w₃ k * net.W₂ k 0| + |net.w₃ k * net.W₂ k 1| +
    |net.w₃ k * net.W₂ k 2| + |net.w₃ k * net.W₂ k 3|)]
  exact effectiveCoefficient_firstFourSum_le net S

end MaxCaterpillar.Fiber.Mixed65
