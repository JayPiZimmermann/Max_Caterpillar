import MaxCaterpillar.Fiber.Count65.Star.PhysicalAdapter
import MaxCaterpillar.Fiber.Count65.Star.Normalize
import MaxCaterpillar.Fiber.Count65.Star.FunctionSpans
import MaxCaterpillar.Fiber.Count65.Star.NoThreeMoving

/-! # Normal forms derived from every actual star physical completion

No head, stationary-core, or residual normal form is an input hypothesis.
The actual network is positively normalized at the second layer, and every
core coefficient comes from one of its original physical neurons.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star
open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65
open MaxCaterpillar.Fiber.Mixed65 (Heads)
open MaxCaterpillar.Fiber.Count65.PhysicalExtraction

structure PhysicalNormalForm (net : Network 4 6 5) (r : ℝ) where
  positiveHead : Fin 5
  negativeHead : Fin 5
  heads_distinct : positiveHead ≠ negativeHead
  positive_output : net.w₃ positiveHead=1
  negative_output : net.w₃ negativeHead = -1
  core : CoefficientSystem (coreIndices positiveHead negativeHead)
  represents : RepresentsStar core r
  original_coefficients : ∀ k,core.out k=net.w₃ k.val ∧
    core.U k=net.W₂ k.val 0 ∧ core.V k=net.W₂ k.val 1 ∧
    core.W k=net.W₂ k.val 2 ∧ core.T k=net.W₂ k.val 3
  stationary : ∀ k∈coreIndices positiveHead negativeHead,
    net.W₂ k 4=0 ∧ net.W₂ k 5=0
  order : Fin 3 ≃ coreIndices positiveHead negativeHead
  carrier_relations :
    (core.reindex order).U 0+(core.reindex order).W 0+(core.reindex order).T 0=0 ∧
    (core.reindex order).W 0+r*(core.reindex order).T 0=0 ∧
    (core.reindex order).T 1=0 ∧
    (core.reindex order).V 1+(core.reindex order).W 1=0
  positive_first : (core.reindex order).out 0=1
  positive_second : (core.reindex order).out 1=1
  negative_third : (core.reindex order).out 2 = -1
  orientations : ∀ i,(core.reindex order).W i=
    if (core.reindex order).W i<0 then -1 else 1
  branches : BranchNormalForm (core.reindex order) r
  corrected_remainder : ∀ q v w : ℝ,
    correctedBase (core.reindex order) r (q,v,w)=max 0 w
  head_identity : (actualHeads net r positiveHead negativeHead).Reconstructs
    (fun x => starBase core r x.1 x.2.1 x.2.2)
  remainder_nonzero : ∃ x : InvariantState,starBase core r x.1 x.2.1 x.2.2≠0
  head_kind : (actualHeads net r positiveHead negativeHead).IsSigned
    (fun x => starBase core r x.1 x.2.1 x.2.2) ∨
    (actualHeads net r positiveHead negativeHead).IsSplitHybrid
      (fun x => starBase core r x.1 x.2.1 x.2.2)

private lemma unit_positive_effective {o w : ℝ} (hu : o=1 ∨ o = -1)
    (he : o*|w|=1) : o=1 ∧ |w|=1 := by
  rcases hu with rfl | rfl
  · simpa using he
  · have ha := abs_nonneg w
    norm_num at he
    linarith only [he,ha]

private lemma unit_negative_effective {o w : ℝ} (hu : o=1 ∨ o = -1)
    (he : o*|w| = -1) : o = -1 ∧ |w|=1 := by
  rcases hu with rfl | rfl
  · have ha := abs_nonneg w
    norm_num at he
    linarith only [he,ha]
  · constructor
    · rfl
    · norm_num at he
      linarith only [he]

/-- Every actual star completion has two physical translation heads, three
original stationary cores in one of the two branches, and exactly one of the
two head reconstruction types, after genuine positive output normalization. -/
theorem exists_physical_normal_form (net : Network 4 6 5) (r : ℝ)
    (hr : 0<r) (hr1 : r≤1) (hW : net.W₁=firstRows r)
    (hmax : ∀ y,net.eval y=Maximum 4 y) :
    Nonempty (PhysicalNormalForm (normalizeSecond net) r) := by
  classical
  have hout : ∀ i,net.w₃ i≠0 := (physical_output_sign_counts net r hr hr1 hW hmax).2.2
  let nn := normalizeSecond net
  have hnnW : nn.W₁=firstRows r := hW
  have hnnmax : ∀ y,nn.eval y=Maximum 4 y := by
    intro y
    rw [normalizeSecond_eval net hout,hmax]
  obtain ⟨p,n,hpn,hp,hn,hstationary⟩ :=
    exists_two_signed_physical_carriers nn r hr hr1 hnnW hnnmax
  have hpunit : nn.w₃ p=1 := by
    rcases normalizeSecond_unit_outputs net hout p with he | he
    · exact he
    · change nn.w₃ p = -1 at he
      linarith only [hp,he]
  have hnunit : nn.w₃ n = -1 := by
    rcases normalizeSecond_unit_outputs net hout n with he | he
    · change nn.w₃ n=1 at he
      linarith only [hn,he]
    · exact he
  have hs : ∀ k∈coreIndices p n,nn.W₂ k 4=0 ∧ nn.W₂ k 5=0 := by
    intro k hk
    have hk' := Finset.mem_erase.mp hk
    have hk'' := Finset.mem_erase.mp hk'.2
    exact hstationary k hk''.1 hk'.1
  obtain ⟨d,hd,horiginal,hheads⟩ :=
    physical_two_head_adapter nn r hnnW hnnmax p n hpn hpunit hnunit hs
  have hc : Fintype.card (coreIndices p n)=3 := by
    rw [Fintype.card_coe,coreIndices_card p n hpn]
  have hu : ∀ k,d.out k=1 ∨ d.out k = -1 := by
    intro k
    rw [(horiginal k).1]
    exact normalizeSecond_unit_outputs net hout k.val
  obtain ⟨e,He,hp0,hp1,hn2,hWne,hu0,ht0,ht1,hv1⟩ :=
    exists_ordered_three d r hr hr1 hd hc
  obtain ⟨he0,he1,he2,hbranch,hbase⟩ :=
    ordered_three_classification (d.reindex e) r hr hr1 He hp0 hp1 hn2
      hWne hu0 ht0 ht1 hv1
  have hu' : ∀ i,(d.reindex e).out i=1 ∨ (d.reindex e).out i = -1 :=
    fun i => hu (e i)
  obtain ⟨ho0,ha0⟩ := unit_positive_effective (hu' 0) he0
  obtain ⟨ho1,ha1⟩ := unit_positive_effective (hu' 1) he1
  obtain ⟨ho2,ha2⟩ := unit_negative_effective (hu' 2) he2
  have habs : ∀ i,|(d.reindex e).W i|=1 := by
    intro i
    fin_cases i
    · exact ha0
    · exact ha1
    · exact ha2
  have hori : ∀ i,(d.reindex e).W i=
      if (d.reindex e).W i<0 then -1 else 1 := by
    intro i
    have he := habs i
    by_cases hneg : (d.reindex e).W i<0
    · rw [if_pos hneg]
      rw [abs_of_neg hneg] at he
      linarith only [he]
    · rw [if_neg hneg]
      rwa [abs_of_nonneg (not_lt.mp hneg)] at he
  have hnz : ∃ x : InvariantState,starBase d r x.1 x.2.1 x.2.2≠0 := by
    by_contra hnz
    push_neg at hnz
    apply (three_gate_signs_and_nonspan d r hr hr1 hd hc).2
    refine ⟨fun _ => 0,?_⟩
    intro q v w
    simpa only [zero_mul,Finset.sum_const_zero] using hnz (q,v,w)
  have hkind := (heads_reconstructs_iff hr (actualHeads nn r p n)
    (fun x => starBase d r x.1 x.2.1 x.2.2)
    (readout_mem_featureSpace r _ _ _ _) (readout_mem_featureSpace r _ _ _ _)
    (readout_mem_featureSpace r _ _ _ _)).mp hheads
  exact ⟨{
    positiveHead := p,negativeHead := n,heads_distinct := hpn
    positive_output := hpunit,negative_output := hnunit
    core := d,represents := hd,original_coefficients := horiginal,stationary := hs
    order := e,carrier_relations := ⟨hu0,ht0,ht1,hv1⟩
    positive_first := ho0,positive_second := ho1,negative_third := ho2
    orientations := hori,branches := hbranch,corrected_remainder := hbase
    head_identity := hheads,remainder_nonzero := hnz,head_kind := hkind }⟩
end MaxCaterpillar.Fiber.Count65.Star
