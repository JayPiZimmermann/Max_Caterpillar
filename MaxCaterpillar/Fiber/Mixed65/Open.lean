import MaxCaterpillar.Fiber.Mixed65.LocalTopology
import MaxCaterpillar.Fiber.First65.LocalRigidity

/-! # The mixed sector is open in the full exact Max4 fiber

The finite strict certificate around each normalized mixed first matrix
forces all nearby exact networks to retain a positively scaled mixed matrix.
Global homeomorphisms implementing the genuine symmetries then transport
these neighborhoods to every point of the full sector.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open Set

/-- Every exact completion of a normalized mixed first matrix is an interior
point of the mixed sector, with all suffix coefficients and biases allowed to vary. -/
theorem seed_mem_interior_sector (net : ExactFiber 4 6 5) (hnet : net ∈ seed) :
    net ∈ interior sector := by
  obtain ⟨t, ht, hrows⟩ := hnet
  apply mem_interior.mpr
  refine ⟨{other : ExactFiber 4 6 5 | LocalCertificate t other.val.W₁}, ?_,
    isOpen_localCertificate_exactFiber t, ?_⟩
  · intro other hcert
    obtain ⟨u, hu, c, hc, hother⟩ :=
      LocalCertificate.scaled_mixed_rows t ht other.val other.property hcert
    exact mem_sector_of_scaled_firstRows other hu c hc hother
  · change LocalCertificate t net.val.W₁
    rw [hrows]
    exact localCertificate_firstRows t ht

/-- Relative openness in the full all-input exact fiber, rather than in a
fixed-first-layer slice or a chosen residual chart. -/
theorem sector_isOpen : IsOpen sector :=
  sector_isOpen_of_seed_interior seed_mem_interior_sector

end MaxCaterpillar.Fiber.Mixed65
