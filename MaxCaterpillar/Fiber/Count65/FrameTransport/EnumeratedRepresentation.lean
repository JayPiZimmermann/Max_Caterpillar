import MaxCaterpillar.Fiber.Count65.FrameTransport.RootSelection
import MaxCaterpillar.Fiber.Count65.ThreeRoots.NetworkBridge

/-! # The maximum representation for any actual invariant-row enumeration -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier TwoRoots

/-- The actual enumeration itself proves that J0 has four elements. -/
theorem invariant_card_of_enumeration (net : Network 4 6 5)
    (e : Fin 4 ≃ invariantRows net) : (invariantRows net).card = 4 := by
  have he := Fintype.card_congr e
  simpa only [Fintype.card_fin,Fintype.card_coe] using he.symm

/-- No particular choice of the four actual invariant rows is privileged.
The decoder is reindexed along the actual equivalences, not assumed to exist. -/
theorem enumerated_represents (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) : Represents (enumeratedRows net e) := by
  obtain ⟨e₀,ell,Phi,hfactor,_⟩ :=
    four_feature_factorization net hnet (invariant_card_of_enumeration net e)
  have h₀ : Represents (enumeratedRows net e₀) := ⟨ell,Phi,hfactor⟩
  have hh := h₀.reindex_rows (e.trans e₀.symm)
  simpa only [enumeratedRows,Equiv.trans_apply,Equiv.apply_symm_apply] using hh

#print axioms enumerated_represents
end MaxCaterpillar.Fiber.Count65.FrameTransport
