import MaxCaterpillar.Fiber.Count65.ForkExclusion.Network
import MaxCaterpillar.Fiber.Symmetry

/-! # The inward-fork exclusion is invariant under first-neuron symmetries -/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion

/-- The actual-network obstruction permits arbitrary positive row scales
and arbitrary first-hidden-neuron order; all biases remain unrestricted. -/
theorem not_exact_network_of_scaled_rows (net : Network 4 6 5) {α β κ : ℝ}
    (hα : 0<α) (hβ : 0<β) (hαβ : α+β=1)
    (hακ : α≤κ) (hβκ : β≤κ) (hκ : κ≠1)
    (p : Equiv.Perm (Fin 6)) (s : Fin 6→ℝ) (hs : ∀ j, 0<s j)
    (hW : ∀ j, net.W₁ (p j)=s j • PhysicalExtraction.carrierRows (invariantRows α β κ) j) :
    ¬ (∀ x, net.eval x=Maximum 4 x) := by
  intro hmax
  let n := scaleFirst (permuteHidden net p (Equiv.refl _)) (fun j => 1/s j)
  have hn : n.W₁=PhysicalExtraction.carrierRows (invariantRows α β κ) := by
    funext j i
    change (1/s j)*net.W₁ (p j) i=PhysicalExtraction.carrierRows (invariantRows α β κ) j i
    rw [congrFun (hW j) i]
    change (1/s j)*(s j*PhysicalExtraction.carrierRows (invariantRows α β κ) j i)=_
    field_simp [ne_of_gt (hs j)]
    ring
  apply not_exact_network n hα hβ hαβ hακ hβκ hκ hn
  intro x
  rw [scaleFirst_eval _ _ (fun j => div_pos (by norm_num) (hs j)),permuteHidden_eval]
  exact hmax x

#print axioms not_exact_network_of_scaled_rows

/-- Input relabelling is permitted as well, so this excludes the entire
physical first-layer symmetry orbit of every admissible inward fork. -/
theorem not_exact_network_of_scaled_permuted_rows (net : Network 4 6 5) {α β κ : ℝ}
    (hα : 0<α) (hβ : 0<β) (hαβ : α+β=1)
    (hακ : α≤κ) (hβκ : β≤κ) (hκ : κ≠1)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (s : Fin 6→ℝ) (hs : ∀ j, 0<s j)
    (hW : ∀ j i, net.W₁ (p j) (q i)=
      s j*PhysicalExtraction.carrierRows (invariantRows α β κ) j i) :
    ¬ (∀ x, net.eval x=Maximum 4 x) := by
  intro hmax
  have hr : ∀ j, (permuteInputs net q).W₁ (p j)=
      s j • PhysicalExtraction.carrierRows (invariantRows α β κ) j := by
    intro j
    funext i
    exact hW j i
  apply not_exact_network_of_scaled_rows (permuteInputs net q)
    hα hβ hαβ hακ hβκ hκ p s hs hr
  intro x
  rw [permuteInputs_eval,hmax,maximum_permute]

#print axioms not_exact_network_of_scaled_permuted_rows
end MaxCaterpillar.Fiber.Count65.ForkExclusion
