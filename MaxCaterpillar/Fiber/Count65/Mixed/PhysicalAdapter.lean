import MaxCaterpillar.Fiber.Mixed65.PhysicalMinimalExtraction
import MaxCaterpillar.Fiber.Count65.Mixed.HeadRemainder

/-! # From two actual carriers to the residual and head classifiers

Only the physical two-carrier support conclusion is an input. The head
reconstruction identity and feature-linear remainder are derived from exact
network evaluation. Every residual incoming coefficient and output weight is
retained from its original physical neuron.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65
open BigOperators MaxCaterpillar.Frontier

noncomputable def coreIndices (p n : Fin 5) : Finset (Fin 5) :=
  (Finset.univ.erase p).erase n

noncomputable def actualHeads (net : Network 4 6 5) (t : ℝ) (p n : Fin 5) :
    Heads InvariantState where
  a := net.W₂ p 4
  b := net.W₂ p 5
  c := net.W₂ n 4
  d := net.W₂ n 5
  A := physicalInvariantPart net t p
  B := physicalInvariantPart net t n

lemma coreIndices_card (p n : Fin 5) (hpn : p ≠ n) : (coreIndices p n).card = 3 := by
  classical
  unfold coreIndices
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hpn,Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _)]
  rfl

private lemma sum_two_heads (p n : Fin 5) (hpn : p ≠ n) (f : Fin 5 → ℝ) :
    (∑ k, f k) = f p + f n + ∑ k in coreIndices p n, f k := by
  classical
  have hp := Finset.sum_erase_add (Finset.univ : Finset (Fin 5)) f (Finset.mem_univ p)
  have hn := Finset.sum_erase_add (Finset.univ.erase p) f
    (Finset.mem_erase.mpr ⟨Ne.symm hpn,Finset.mem_univ n⟩)
  change (∑ k in coreIndices p n, f k) + f n = ∑ k in Finset.univ.erase p, f k at hn
  linarith only [hp,hn]

/-- Exact evaluation over two identified actual carriers supplies both a
three-core residual system and the head identity, without assuming either. -/
theorem physical_two_head_adapter (net : Network 4 6 5) (t : ℝ)
    (hW : net.W₁ = firstRows t) (hmax : ∀ y, net.eval y = Maximum 4 y)
    (p n : Fin 5) (hpn : p ≠ n) (hp : net.w₃ p = 1) (hn : net.w₃ n = -1)
    (hstationary : ∀ k ∈ coreIndices p n, net.W₂ k 4 = 0 ∧ net.W₂ k 5 = 0) :
    ∃ d : ResidualSystem (coreIndices p n), d.Represents t ∧
      (∀ k, d.out k = net.w₃ k.val ∧ d.U k = net.W₂ k.val 0 ∧
        d.V k = net.W₂ k.val 1 ∧ d.W k = net.W₂ k.val 2 ∧ d.T k = net.W₂ k.val 3) ∧
      (actualHeads net t p n).Reconstructs
        (fun x => d.base t x.1 x.2.1 x.2.2) := by
  classical
  let K : InvariantState → ℝ := fun x => invariantTarget x -
    ∑ k in coreIndices p n, net.w₃ k * relu (physicalInvariantPart net t k x)
  have hheads : (actualHeads net t p n).Reconstructs K := by
    intro x z
    have he := physical_recession_signed_carrier_identity net t hW hmax x z
    rw [sum_two_heads p n hpn] at he
    have hc : (∑ k in coreIndices p n,
        net.w₃ k * relu (net.W₂ k 4*relu z+net.W₂ k 5*relu (-z)+
          physicalInvariantPart net t k x)) =
        ∑ k in coreIndices p n, net.w₃ k * relu (physicalInvariantPart net t k x) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [(hstationary k hk).1,(hstationary k hk).2]
      simp only [zero_mul,zero_add]
    rw [hc,hp,hn,one_mul,neg_one_mul] at he
    dsimp only [Heads.eval,actualHeads,K]
    linarith only [he]
  have hmem : K ∈ featureSpace t := hheads.remainder_mem (featureSpace t)
    (readout_mem_featureSpace t _ _ _ _) (readout_mem_featureSpace t _ _ _ _)
  obtain ⟨A,B,C,D,hK⟩ := hmem
  let d : ResidualSystem (coreIndices p n) := {
    lU := A, lV := B, lW := C, lT := D
    out := fun k => net.w₃ k.val
    U := fun k => net.W₂ k.val 0
    V := fun k => net.W₂ k.val 1
    W := fun k => net.W₂ k.val 2
    T := fun k => net.W₂ k.val 3 }
  have hbase : ∀ x : InvariantState, d.base t x.1 x.2.1 x.2.2 = K x := by
    intro x
    exact (congrFun hK x).symm
  refine ⟨d,?_,?_,?_⟩
  · intro q b c
    change invariantTarget (q,b,c) = d.base t q b c +
      ∑ k : coreIndices p n, net.w₃ k.val * relu (d.gate t k q b c)
    rw [hbase (q,b,c)]
    change invariantTarget (q,b,c) = K (q,b,c) +
      ∑ k : coreIndices p n, net.w₃ k.val * relu (physicalInvariantPart net t k.val (q,b,c))
    rw [Finset.sum_coe_sort (coreIndices p n)
      (fun k => net.w₃ k * relu (physicalInvariantPart net t k (q,b,c)))]
    dsimp only [K]
    ring
  · intro k
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · intro x z
    change (actualHeads net t p n).eval x z = z + d.base t x.1 x.2.1 x.2.2
    rw [hbase x]
    exact hheads x z

end MaxCaterpillar.Fiber.Mixed65
