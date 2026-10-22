import MaxCaterpillar.KMPS
import MaxCaterpillar.SharingRational

/-! # CPWL networks with rational parameters

Version 2 of `cpwl_two_hidden_layers_pieces` (Version 1, in `KMPS.lean`):
the KMPS representation uses the affine functions of the given witness
unchanged, so rational witness data give a network with rational weights and
biases, and linear witness functions give zero biases.
-/

open BigOperators

namespace MaxCaterpillar

/-- Version 2: for `d ≥ 2` and a CPWL witness whose affine functions have
rational coefficients and offsets, the network of
`cpwl_two_hidden_layers_pieces` has rational weights and biases; if every
witness function is linear, it has zero biases. Version 1 is
`cpwl_two_hidden_layers_pieces`. -/
theorem cpwl_two_hidden_layers_pieces_rational (d : ℕ) (hd : 2 ≤ d) (f : Point d → ℝ)
    (hf : f ∈ MaxNN.CPWL d) (W : MaxNN.CPWLWitness d f)
    (ha : ∀ i l, ∃ q : ℚ, (q : ℝ) = (W.g i).a l) (hc : ∀ i, ∃ q : ℚ, (q : ℝ) = (W.g i).c) :
    ∃ (T : ℕ) (α : Fin T → Fin (d + 1) → Fin W.n) (ε : Fin T → ℝ),
      (∀ t, ε t = 1 ∨ ε t = -1) ∧
      (∀ x, f x = ∑ t, ε t * Maximum (d + 1)
        (fun i => (∑ l, (W.g (α t i)).a l * x l) + (W.g (α t i)).c)) ∧
      ∃ s : ℕ, s = (Finset.univ.image fun t => Finset.univ.image (α t)).card ∧ s ≤ T ∧
        ∃ net : Network d (W.n.choose 2 + W.n + 1) (s * (secondWidth (d + 1) - 2) + 2),
          (∀ x, net.eval x = f x) ∧ net.HasRationalWeights ∧ net.HasRationalBiases ∧
            ((∀ i, (W.g i).c = 0) → net.HasZeroBiases) := by
  obtain ⟨T, ε, α, hε, hrep⟩ := kmps_pieces d f hf W
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
  have hεq : ∀ t, ∃ q : ℚ, (q : ℝ) = ε t := fun t => by
    rcases hε t with h | h
    · exact ⟨1, by rw [h]; norm_num⟩
    · exact ⟨-1, by rw [h]; norm_num⟩
  obtain ⟨net, hnet, hw, hb, hz⟩ := caterpillar_shared_pieces_rational_pieces r (by omega)
    (fun a => (W.g a).a) (fun a => (W.g a).c) α ε ha hc hεq
  exact ⟨T, α, ε, hε, hrep, _, rfl, card_imageSets_le α, net,
    fun x => (hnet x).trans (hrep x).symm, hw, hb, fun h0 => hz (funext h0)⟩

end MaxCaterpillar
