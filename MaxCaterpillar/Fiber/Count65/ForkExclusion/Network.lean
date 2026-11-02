import MaxCaterpillar.Fiber.Count65.ForkExclusion.AllParameters
import MaxCaterpillar.Fiber.Count65.PhysicalExtraction.Coordinates

/-! # The inward-fork obstruction for actual physical networks

This uses the proven signed-carrier extraction theorem, not an assumed
residual normal form. All original network biases are permitted.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion
open BigOperators MaxCaterpillar.Frontier

noncomputable def invariantRows (α β κ : ℝ) : Fin 4→Point 3 :=
  ![![1,0,0],![0,1,0],![-α,-β,1],![-α,-β,κ]]

noncomputable def coeffOf (f : Fin 4→ℝ) : Coeff := ⟨f 0,f 1,f 2,f 3⟩

lemma feature_sum (α β κ u v w : ℝ) (f : Fin 4→ℝ) :
    (∑ a, f a*PhysicalExtraction.features (invariantRows α β κ) (![u,v,w]) a) =
      form α β κ (coeffOf f) u v w := by
  have h3 : (Fin.succ (2 : Fin 3) : Fin 4)=3 := rfl
  simp [PhysicalExtraction.features,invariantRows,coeffOf,form,lin,Fin.sum_univ_succ,h3]
  ring

lemma target_frame (u v w : ℝ) :
    PhysicalExtraction.target (![u,v,w])=target u v w := by
  change max (max u v) (relu w)=max (max 0 u) (max v w)
  simp only [relu,max_assoc,max_comm,max_left_comm]

/-- No ordinary width-(6,5) network with this normalized inward-fork first
layer computes Max4 on all real inputs, even with arbitrary real biases. -/
theorem not_exact_network (net : Network 4 6 5) {α β κ : ℝ}
    (hα : 0<α) (hβ : 0<β) (hαβ : α+β=1)
    (hακ : α≤κ) (hβκ : β≤κ) (hκ : κ≠1)
    (hW : net.W₁=PhysicalExtraction.carrierRows (invariantRows α β κ)) :
    ¬ (∀ x, net.eval x=Maximum 4 x) := by
  classical
  intro hmax
  obtain ⟨S,hS,R,hR⟩ := PhysicalExtraction.physical_residual_at_most_three
    net (invariantRows α β κ) hW hmax
  let d : ResidualSystem S :=
    ⟨coeffOf R,fun j => coeffOf (fun a => net.W₂ j (Fin.castAdd 2 a)),fun j => net.w₃ j⟩
  have hd : d.Represents α β κ := by
    intro u v w
    have hh := hR (![u,v,w])
    rw [target_frame,feature_sum] at hh
    have hg : ∀ j : Fin 5,
        PhysicalExtraction.invariantPart net (invariantRows α β κ) j (![u,v,w]) =
          form α β κ (coeffOf (fun a => net.W₂ j (Fin.castAdd 2 a))) u v w := by
      intro j
      exact feature_sum α β κ u v w _
    simp_rw [hg] at hh
    change target u v w=form α β κ (coeffOf R) u v w+
      ∑ j : S, net.w₃ j*relu
        (form α β κ (coeffOf (fun a => net.W₂ j (Fin.castAdd 2 a))) u v w)
    have hsum : (∑ j : S, net.w₃ j*relu
        (form α β κ (coeffOf (fun a => net.W₂ j (Fin.castAdd 2 a))) u v w)) =
        ∑ j in S, net.w₃ j*relu
        (form α β κ (coeffOf (fun a => net.W₂ j (Fin.castAdd 2 a))) u v w) :=
      Finset.sum_coe_sort (s := S) (f := fun j : Fin 5 => net.w₃ j*relu
        (form α β κ (coeffOf (fun a => net.W₂ j (Fin.castAdd 2 a))) u v w))
    rw [hsum]
    exact hh
  have hc := d.card_ge_four hα hβ hαβ hακ hβκ hκ hd
  rw [Fintype.card_coe] at hc
  linarith only [hc,hS]

#print axioms not_exact_network
end MaxCaterpillar.Fiber.Count65.ForkExclusion
