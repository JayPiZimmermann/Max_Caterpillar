import MaxCaterpillar.Fiber.Mixed65.Construction
import MaxCaterpillar.Fiber.Mixed65.Extraction
import MaxCaterpillar.Fiber.Mixed65.FeatureSpace

/-! # Diagonal extraction from actual mixed-dictionary networks

The hypotheses here concern the original six parameter arrays of an ordinary
network. We evaluate on an explicit invertible change of input coordinates,
then apply the finite signed-carrier extraction theorem. No residual
classification or assumed hidden-layer normal form enters the adapter.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators MaxCaterpillar.Frontier

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
        relu (t * x.1 - x.2.1), relu z, relu (-z)] := by
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
  norm_num [Fin.sum_univ_succ, physicalInvariantPart, readout, form]
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

/-- Both diagonal tails of an arbitrary physical completion over the mixed
first dictionary, including zero slopes and arbitrary signed output weights. -/
theorem physical_diagonal_extraction (net : Network 4 6 m) (t : ℝ)
    (hz : net.HasZeroBiases) (hW : net.W₁ = firstRows t)
    (hmax : ∀ y, net.eval y = Maximum 4 y) :
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
    (physical_signed_carrier_identity net t hz hW hmax)

end MaxCaterpillar.Fiber.Mixed65
