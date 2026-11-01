import MaxCaterpillar.Fiber.Mixed65.PhysicalExtraction
import MaxCaterpillar.Fiber.Mixed65.MinimalExtraction
import MaxCaterpillar.Fiber.Mixed65.CarrierForcing

/-! # Three unchanged residual gates in every physical mixed completion

The residual lower bound is proved by `ResidualSystem.card_ge_three`, rather
than assumed. Applied to the actual diagonal tails it gives the zero-slope
cardinalities needed for five-gate extraction. The arbitrary-bias statements
use recession: all three weight arrays stay unchanged while biases are erased.
Consequently the extracted residual gates have the original incoming and
outgoing coefficients, interpreted in the homogeneous recession network.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators MaxCaterpillar.Frontier

variable {m : ℕ}

/-- Collecting a linear combination changes only the four remainder
coefficients; it does not change any original residual gate. -/
theorem physicalInvariantPart_linearCombination (net : Network 4 6 m)
    (t : ℝ) (l : Fin m → ℝ) (x : InvariantState) :
    (∑ j, l j * physicalInvariantPart net t j x) =
      readout t (∑ j, l j * net.W₂ j 0) (∑ j, l j * net.W₂ j 1)
        (∑ j, l j * net.W₂ j 2) (∑ j, l j * net.W₂ j 3) x := by
  simp only [physicalInvariantPart, readout, form, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]

/-- The extracted system retains the selected physical gate coefficients;
only the remainder is collected into four coefficients. -/
noncomputable def physicalResidualSystem (net : Network 4 6 m)
    (S : Finset (Fin m)) (l : Fin m → ℝ) : ResidualSystem S := {
    lU := ∑ j, l j * net.W₂ j 0
    lV := ∑ j, l j * net.W₂ j 1
    lW := ∑ j, l j * net.W₂ j 2
    lT := ∑ j, l j * net.W₂ j 3
    out := fun j => net.w₃ j.val
    U := fun j => net.W₂ j.val 0
    V := fun j => net.W₂ j.val 1
    W := fun j => net.W₂ j.val 2
    T := fun j => net.W₂ j.val 3 }

theorem physicalResidualSystem_represents (net : Network 4 6 m) (t : ℝ)
    (S : Finset (Fin m)) (l : Fin m → ℝ)
    (h : ∀ x : InvariantState, invariantTarget x =
      (∑ j, l j * physicalInvariantPart net t j x) +
        ∑ j in S, net.w₃ j * relu (physicalInvariantPart net t j x)) :
    (physicalResidualSystem net S l).Represents t := by
  intro q b c
  have hh := h (q, b, c)
  rw [physicalInvariantPart_linearCombination] at hh
  change invariantTarget (q, b, c) =
    readout t (∑ j, l j * net.W₂ j 0) (∑ j, l j * net.W₂ j 1)
      (∑ j, l j * net.W₂ j 2) (∑ j, l j * net.W₂ j 3) (q, b, c) +
    ∑ j : S, net.w₃ j.val * relu (physicalInvariantPart net t j.val (q, b, c))
  rw [Finset.sum_coe_sort S
    (fun j => net.w₃ j * relu (physicalInvariantPart net t j (q, b, c)))]
  exact hh

/-- The arbitrary finite residual floor, applied to any subset of actual
physical neurons and any feature-linear remainder. -/
theorem physical_residual_card_ge_three (net : Network 4 6 m) (t : ℝ)
    (ht : 0 < t) (S : Finset (Fin m)) (l : Fin m → ℝ)
    (h : ∀ x : InvariantState, invariantTarget x =
      (∑ j, l j * physicalInvariantPart net t j x) +
        ∑ j in S, net.w₃ j * relu (physicalInvariantPart net t j x)) :
    3 ≤ S.card := by
  classical
  simpa only [Fintype.card_coe] using
    (physicalResidualSystem net S l).card_ge_three t ht
      (physicalResidualSystem_represents net t S l h)

/-- Recession erases biases and preserves every weight entering the extracted
identity. This is a statement about the homogeneous coefficient identity. -/
theorem physical_recession_signed_carrier_identity (net : Network 4 6 m) (t : ℝ)
    (hW : net.W₁ = firstRows t) (hmax : ∀ y, net.eval y = Maximum 4 y) :
    ∀ x z, (∑ j, net.w₃ j * relu (net.W₂ j 4 * relu z +
      net.W₂ j 5 * relu (-z) + physicalInvariantPart net t j x)) =
        z + invariantTarget x := by
  have hzmax : ∀ y, net.zeroBias.eval y = Maximum 4 y :=
    net.eval_zeroBias_of_posHom (Maximum 4) (fun c hc y => Maximum_smul hc y) hmax
  exact physical_signed_carrier_identity net.zeroBias t net.zeroBias_hasZeroBiases hW hzmax

/-- Both diagonal tails are valid with arbitrary original biases, because the
underlying weight arrays are unchanged by the proved recession operation. -/
theorem physical_recession_diagonal_extraction (net : Network 4 6 m) (t : ℝ)
    (hW : net.W₁ = firstRows t) (hmax : ∀ y, net.eval y = Maximum 4 y) :
    (∑ j in Finset.univ.filter (fun j => 0 < net.W₂ j 4),
      net.w₃ j * net.W₂ j 4) = 1 ∧
    (∑ j in Finset.univ.filter (fun j => 0 < net.W₂ j 5),
      net.w₃ j * net.W₂ j 5) = -1 ∧
    ∀ x : InvariantState,
      (invariantTarget x =
        (∑ j in Finset.univ.filter (fun j => 0 < net.W₂ j 4),
          net.w₃ j * physicalInvariantPart net t j x) +
        ∑ j in Finset.univ.filter (fun j => net.W₂ j 4 = 0),
          net.w₃ j * relu (physicalInvariantPart net t j x)) ∧
      (invariantTarget x =
        (∑ j in Finset.univ.filter (fun j => 0 < net.W₂ j 5),
          net.w₃ j * physicalInvariantPart net t j x) +
        ∑ j in Finset.univ.filter (fun j => net.W₂ j 5 = 0),
          net.w₃ j * relu (physicalInvariantPart net t j x)) := by
  classical
  exact finite_signed_carrier_extraction net.w₃ (fun j => net.W₂ j 4)
    (fun j => net.W₂ j 5) (physicalInvariantPart net t) invariantTarget
    (physical_recession_signed_carrier_identity net t hW hmax)

/-- Each translation tail leaves at least three neurons with zero slope.
No output sign or nonzero-weight hypothesis is imposed. -/
theorem physical_zero_carrier_cards (net : Network 4 6 m) (t : ℝ) (ht : 0 < t)
    (hW : net.W₁ = firstRows t) (hmax : ∀ y, net.eval y = Maximum 4 y) :
    3 ≤ (Finset.univ.filter fun j => net.W₂ j 4 = 0).card ∧
    3 ≤ (Finset.univ.filter fun j => net.W₂ j 5 = 0).card := by
  classical
  obtain ⟨_, _, hrem⟩ := physical_recession_diagonal_extraction net t hW hmax
  constructor
  · apply physical_residual_card_ge_three net t ht
      (Finset.univ.filter fun j => net.W₂ j 4 = 0)
      (fun j => if 0 < net.W₂ j 4 then net.w₃ j else 0)
    intro x
    convert (hrem x).1 using 1
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj <;> simp [hj]
  · apply physical_residual_card_ge_three net t ht
      (Finset.univ.filter fun j => net.W₂ j 5 = 0)
      (fun j => if 0 < net.W₂ j 5 then net.w₃ j else 0)
    intro x
    convert (hrem x).2 using 1
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj <;> simp [hj]

/-- Every exact physical width-(6,5) completion over the mixed first matrix
contains three original residual gates with unchanged invariant coefficients
and unchanged output weights. Only the linear remainder is recombined.
Arbitrary biases are covered through recession. -/
theorem physical_three_gate_extraction (net : Network 4 6 5) (t : ℝ) (ht : 0 < t)
    (hW : net.W₁ = firstRows t) (hmax : ∀ y, net.eval y = Maximum 4 y) :
    ∃ S : Finset (Fin 5), S.card = 3 ∧ ∃ l : Fin 5 → ℝ,
      ∀ x : InvariantState, invariantTarget x =
        (∑ j, l j * physicalInvariantPart net t j x) +
          ∑ j in S, net.w₃ j * relu (physicalInvariantPart net t j x) := by
  obtain ⟨ha, hb⟩ := physical_zero_carrier_cards net t ht hW hmax
  exact five_gate_residual_extraction net.w₃ (fun j => net.W₂ j 4)
    (fun j => net.W₂ j 5) (physicalInvariantPart net t) invariantTarget
    (physical_recession_signed_carrier_identity net t hW hmax) ha hb

end MaxCaterpillar.Fiber.Mixed65
