import MaxCaterpillar.Fiber.Count65.RootFrameTable
import MaxCaterpillar.Fiber.Count65.RootFrames

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.RootFrames

/-- Exact all-real classification: the decoder is arbitrary and no coefficient
alphabet is assumed. Integer certificates only exclude impossible directions. -/
theorem four_roots_normal_form (F : Frame) (hcard : F.card = 4)
    (hloop : NoLoops F) (hcover : CoversTriples F) (hf : Factors F) : NormalForm F := by
  rcases four_roots_checked_alternative F hcard hloop hcover with hbad | hgood
  · obtain ⟨w, hw⟩ := hbad
    exact False.elim (not_factors_of_checked F w hw hf)
  · exact hgood
end MaxCaterpillar.Fiber.Count65.RootFrames
