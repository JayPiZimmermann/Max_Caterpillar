import MaxCaterpillar.Fiber.Star65.Construction
import MaxCaterpillar.Fiber.Mixed65.Extraction
import MaxCaterpillar.Fiber.Count65.Star.FeatureSpace
import MaxCaterpillar.Fiber.Count65.PhysicalExtraction

/-! # Diagonal extraction from actual star-dictionary networks

The hypotheses here concern the original six parameter arrays of an ordinary
network. We evaluate on an explicit invertible change of input coordinates,
then apply the finite signed-carrier extraction theorem. No residual
classification or assumed hidden-layer normal form enters the adapter.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Star

open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65
open MaxCaterpillar.Fiber.Mixed65 (finite_signed_carrier_extraction)

variable {m : ℕ}

/-- Independent invariant coordinates together with the common translation. -/
noncomputable def translatedInput (x : InvariantState) (z : ℝ) : Point 4 :=
  ![x.1 + x.2.1 + z, x.2.1 + z, z, x.2.2 + z]

/-- Max4 after subtracting the common translation coordinate. -/
noncomputable def invariantTarget (x : InvariantState) : ℝ :=
  max (max (x.1 + x.2.1) x.2.1) (relu x.2.2)

/-- The invariant part of the actual second-neuron preactivation. The four
coefficients are taken unchanged from the physical second weight matrix. -/
noncomputable def physicalInvariantPart (net : Network 4 6 m) (t : ℝ)
    (j : Fin m) : InvariantState → ℝ :=
  readout t (net.W₂ j 0) (net.W₂ j 1) (net.W₂ j 2) (net.W₂ j 3)

theorem physicalInvariantPart_mem (net : Network 4 6 m) (t : ℝ) (j : Fin m) :
    physicalInvariantPart net t j ∈ featureSpace t :=
  readout_mem_featureSpace t _ _ _ _

theorem translatedInput_coordinates (x : InvariantState) (z : ℝ) :
    (translatedInput x z 0 - translatedInput x z 1 = x.1) ∧
    (translatedInput x z 1 - translatedInput x z 2 = x.2.1) ∧
    (translatedInput x z 3 - translatedInput x z 2 = x.2.2) ∧
    translatedInput x z 2 = z := by
  change (x.1 + x.2.1 + z - (x.2.1 + z) = x.1) ∧
    (x.2.1 + z - z = x.2.1) ∧ (x.2.2 + z - z = x.2.2) ∧ z = z
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · rfl

theorem maximum_translatedInput (x : InvariantState) (z : ℝ) :
    Maximum 4 (translatedInput x z) = z + invariantTarget x := by
  rw [Maximum_four]
  change max (max (x.1 + x.2.1 + z) (x.2.1 + z)) (max z (x.2.2 + z)) =
    z + max (max (x.1 + x.2.1) x.2.1) (max 0 x.2.2)
  have hz : max z (x.2.2 + z) = max 0 x.2.2 + z := by
    simpa only [zero_add] using (max_add_add_right (0 : ℝ) x.2.2 z)
  rw [max_add_add_right, hz, max_add_add_right]
  ring

theorem firstValues_translatedInput (t : ℝ) (x : InvariantState) (z : ℝ) :
    firstValues t (translatedInput x z) =
      ![relu x.1, relu x.2.1, relu x.2.2,
        relu (x.1 + t * x.2.1), relu z, relu (-z)] := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := translatedInput_coordinates x z
  rw [firstValues, h₀, h₁, h₂, h₃]

/-- Exact evaluation in translated coordinates, without using the output target. -/
theorem physical_eval_translatedInput (net : Network 4 6 m) (t : ℝ)
    (hz : net.HasZeroBiases) (hW : net.W₁ = firstRows t)
    (x : InvariantState) (z : ℝ) :
    net.eval (translatedInput x z) =
      ∑ j, net.w₃ j * relu (net.W₂ j 4 * relu z +
        net.W₂ j 5 * relu (-z) + physicalInvariantPart net t j x) := by
  rcases hz with ⟨hb₁, hb₂, hb₃⟩
  simp only [Network.eval, hW, hb₁, hb₂, hb₃, Pi.zero_apply, add_zero]
  simp_rw [firstRows_eval, firstValues_translatedInput]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  norm_num [Fin.sum_univ_succ, physicalInvariantPart, readout, starLinearForm, relu]
  simp only [show (Fin.succ (2 : Fin 5) : Fin 6) = 3 from rfl,
    show (Fin.succ (Fin.succ (2 : Fin 4)) : Fin 6) = 4 from rfl,
    show (Fin.succ (Fin.succ (Fin.succ (2 : Fin 3))) : Fin 6) = 5 from rfl]
  ring

/-- The full signed-carrier identity is a consequence of all-input exactness of
the actual network. Both output weights and all second incoming weights remain
the original ones; no scaling or gate normalization is performed. -/
theorem physical_signed_carrier_identity (net : Network 4 6 m) (t : ℝ)
    (hz : net.HasZeroBiases) (hW : net.W₁ = firstRows t)
    (hmax : ∀ y, net.eval y = Maximum 4 y) :
    ∀ x z, (∑ j, net.w₃ j * relu (net.W₂ j 4 * relu z +
      net.W₂ j 5 * relu (-z) + physicalInvariantPart net t j x)) =
        z + invariantTarget x := by
  intro x z
  rw [← physical_eval_translatedInput net t hz hW x z, hmax,
    maximum_translatedInput]

/-- Arbitrary original biases are permitted: recession preserves all weights
and gives the same exact signed-carrier identity. -/
theorem physical_signed_carrier_identity_any_bias (net : Network 4 6 m) (r : ℝ)
    (hW : net.W₁ = firstRows r)
    (hmax : ∀ y, net.eval y = Maximum 4 y) :
    ∀ x z, (∑ j, net.w₃ j * relu (net.W₂ j 4 * relu z +
      net.W₂ j 5 * relu (-z) + physicalInvariantPart net r j x)) =
        z + invariantTarget x := by
  have hzero : ∀ y, net.zeroBias.eval y = Maximum 4 y :=
    net.eval_zeroBias_of_posHom (Maximum 4) (fun c hc y => Maximum_smul hc y) hmax
  exact physical_signed_carrier_identity net.zeroBias r ⟨rfl,rfl,rfl⟩ hW hzero

/-- An actual physical completion supplies at most three unchanged residual
cores in the complete invariant input domain. -/
theorem physical_residual_at_most_three (net : Network 4 6 5) (r : ℝ)
    (hW : net.W₁ = firstRows r)
    (hmax : ∀ y, net.eval y = Maximum 4 y) :
    ∃ S : Finset (Fin 5), S.card ≤ 3 ∧ ∃ R : InvariantState → ℝ,
      R ∈ featureSpace r ∧ ∀ x, invariantTarget x = R x +
        ∑ j in S, net.w₃ j * relu (physicalInvariantPart net r j x) := by
  classical
  obtain ⟨S,hS,l,hl⟩ :=
    MaxCaterpillar.Fiber.Count65.PhysicalExtraction.five_gate_residual_extraction_le_three
      net.w₃ (fun j => net.W₂ j 4) (fun j => net.W₂ j 5)
      (physicalInvariantPart net r) invariantTarget
      (physical_signed_carrier_identity_any_bias net r hW hmax)
  refine ⟨S,hS,fun x => ∑ j, l j * physicalInvariantPart net r j x,?_,hl⟩
  have hm := (featureSpace r).sum_mem (t := Finset.univ) (fun j _ =>
    (featureSpace r).smul_mem (l j) (physicalInvariantPart_mem net r j))
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hm

end MaxCaterpillar.Fiber.Count65.Star
