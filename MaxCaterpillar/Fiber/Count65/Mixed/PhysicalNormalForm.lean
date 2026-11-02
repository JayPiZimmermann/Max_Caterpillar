import MaxCaterpillar.Fiber.Count65.Mixed.PhysicalAdapter
import MaxCaterpillar.Fiber.Count65.Mixed.NormalizedResidual
import MaxCaterpillar.Fiber.Count65.Mixed.ResidualNonzero
import MaxCaterpillar.Fiber.Count65.PhysicalExtraction.NoThreeMoving

/-! # Derived normal forms of every actual mixed physical completion

The network is arbitrary over the mixed first matrix. Positive second-neuron
scaling is the proved physical symmetry. Its five original neurons supply
three stationary cores and two opposite-output heads; no head or residual
normal-form identity is an assumption.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65
open MaxCaterpillar.Frontier
open MaxCaterpillar.Fiber.Count65.PhysicalExtraction

/-- All fields refer to the actual network coefficients. This is a derived
classification certificate, not the definition of an exact physical network. -/
structure PhysicalNormalForm (net : Network 4 6 5) (t : ℝ) where
  positiveHead : Fin 5
  negativeHead : Fin 5
  heads_distinct : positiveHead ≠ negativeHead
  positive_output : net.w₃ positiveHead = 1
  negative_output : net.w₃ negativeHead = -1
  core : ResidualSystem (coreIndices positiveHead negativeHead)
  represents : core.Represents t
  original_coefficients : ∀ k, core.out k = net.w₃ k.val ∧
    core.U k = net.W₂ k.val 0 ∧ core.V k = net.W₂ k.val 1 ∧
    core.W k = net.W₂ k.val 2 ∧ core.T k = net.W₂ k.val 3
  stationary : ∀ k ∈ coreIndices positiveHead negativeHead,
    net.W₂ k 4 = 0 ∧ net.W₂ k 5 = 0
  order : Fin 3 ≃ coreIndices positiveHead negativeHead
  positive_first : (core.reindex order).out 0 = 1
  positive_second : (core.reindex order).out 1 = 1
  negative_third : (core.reindex order).out 2 = -1
  orientations : ∀ i, (core.reindex order).W i =
    if (core.reindex order).W i < 0 then -1 else 1
  branches : (∃ k : ℝ, 1 ≤ t*k ∧ (core.reindex order).HasADirections t k) ∨
    (∃ r : ℝ, 1+t ≤ t*r ∧ (core.reindex order).HasBDirections t r)
  head_identity : (actualHeads net t positiveHead negativeHead).Reconstructs
    (fun x => core.base t x.1 x.2.1 x.2.2)
  remainder_nonzero : ∃ x : InvariantState, core.base t x.1 x.2.1 x.2.2 ≠ 0
  head_kind : (actualHeads net t positiveHead negativeHead).IsSigned
    (fun x => core.base t x.1 x.2.1 x.2.2) ∨
    (actualHeads net t positiveHead negativeHead).IsSplitHybrid
      (fun x => core.base t x.1 x.2.1 x.2.2)

/-- Every actual mixed completion admits the complete stationary-core and
head classification after genuine positive physical output normalization.
Arbitrary original biases are handled by the proved recession identity. -/
theorem exists_physical_normal_form (net : Network 4 6 5) (t : ℝ) (ht : 0 < t)
    (hW : net.W₁ = firstRows t) (hmax : ∀ y, net.eval y = Maximum 4 y) :
    Nonempty (PhysicalNormalForm (normalizeSecond net) t) := by
  classical
  have hout : ∀ i, net.w₃ i ≠ 0 := (physical_output_sign_counts net t ht hW hmax).2.2
  let nn := normalizeSecond net
  have hnnW : nn.W₁ = firstRows t := hW
  have hnnmax : ∀ y, nn.eval y = Maximum 4 y := by
    intro y
    rw [normalizeSecond_eval net hout,hmax]
  obtain ⟨p,n,hpn,hp,hn,hstationary⟩ :=
    exists_two_signed_physical_carriers nn t ht hnnW hnnmax
  have hpunit : nn.w₃ p = 1 := by
    rcases normalizeSecond_unit_outputs net hout p with he | he
    · exact he
    · change nn.w₃ p = -1 at he
      linarith only [hp,he]
  have hnunit : nn.w₃ n = -1 := by
    rcases normalizeSecond_unit_outputs net hout n with he | he
    · change nn.w₃ n = 1 at he
      linarith only [hn,he]
    · exact he
  have hs : ∀ k ∈ coreIndices p n, nn.W₂ k 4 = 0 ∧ nn.W₂ k 5 = 0 := by
    intro k hk
    have hk' := Finset.mem_erase.mp hk
    have hk'' := Finset.mem_erase.mp hk'.2
    exact hstationary k hk''.1 hk'.1
  obtain ⟨d,hd,horiginal,hheads⟩ := physical_two_head_adapter nn t hnnW hnnmax
    p n hpn hpunit hnunit hs
  have hcard : Fintype.card (coreIndices p n) = 3 := by
    rw [Fintype.card_coe,coreIndices_card p n hpn]
  have hunit : ∀ k, d.out k = 1 ∨ d.out k = -1 := by
    intro k
    rw [(horiginal k).1]
    exact normalizeSecond_unit_outputs net hout k.val
  obtain ⟨e,_,h0,h1,h2,hori,hbranches⟩ :=
    d.exists_unit_output_normal_form t ht hd hcard hunit
  have hkind := (Heads.reconstructs_iff_signed_or_splitHybrid (featureSpace t)
    (featureSpace_clipping_rigid ht) (actualHeads nn t p n)
    (fun x => d.base t x.1 x.2.1 x.2.2)
    (readout_mem_featureSpace t _ _ _ _) (readout_mem_featureSpace t _ _ _ _)
    (readout_mem_featureSpace t _ _ _ _)).mp hheads
  exact ⟨{
    positiveHead := p, negativeHead := n, heads_distinct := hpn
    positive_output := hpunit, negative_output := hnunit
    core := d, represents := hd, original_coefficients := horiginal
    stationary := hs, order := e
    positive_first := h0, positive_second := h1, negative_third := h2
    orientations := hori, branches := hbranches, head_identity := hheads
    remainder_nonzero := d.exists_nonzero_base t ht hd hcard
    head_kind := hkind }⟩

end MaxCaterpillar.Fiber.Mixed65
