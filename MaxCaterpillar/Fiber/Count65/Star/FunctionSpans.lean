import MaxCaterpillar.Fiber.Count65.Star.Normalize
import MaxCaterpillar.Fiber.Count65.Star.SignSpans
import MaxCaterpillar.Fiber.Count65.PhysicalExtraction.HalfLineRigidity
import MaxCaterpillar.Fiber.JumpBalance

/-! # Actual sign domains and the nonparallel remainder of every star residual -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star
open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65
open MaxCaterpillar.Fiber.Count65.PhysicalExtraction

lemma FullSignSpan.coreSignRigid {r : ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hs : FullSignSpan r g) :
    CoreSignRigid (featureSpace r) (fun x : InvariantState => g x.1 x.2.1 x.2.2) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · by_contra hn
    have hz := (hs 0 0 1 0).2 (by
      intro q v w hc
      exact False.elim (hn ⟨(q,v,w),hc⟩))
    norm_num at hz
  · by_contra hn
    have hz := (hs 0 0 1 0).1 (by
      intro q v w hc
      exact False.elim (hn ⟨(q,v,w),hc⟩))
    norm_num at hz
  · intro F hF hzero
    obtain ⟨A,B,C,D,rfl⟩ := hF
    obtain ⟨rfl,rfl,rfl,rfl⟩ := (hs A B C D).2 (by
      intro q v w hc
      exact hzero (q,v,w) hc)
    intro x
    simp [readout,starLinearForm]
  · intro F hF hzero
    obtain ⟨A,B,C,D,rfl⟩ := hF
    obtain ⟨rfl,rfl,rfl,rfl⟩ := (hs A B C D).1 (by
      intro q v w hc
      exact hzero (q,v,w) hc)
    intro x
    simp [readout,starLinearForm]

lemma fullSignSpan_unnormalize {r w : ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hw : w ≠ 0) (hs : FullSignSpan r (fun q v z => g q v z / (-w))) :
    FullSignSpan r g := by
  have he : ∀ q v z, (-w)*(g q v z/(-w))=g q v z := by
    intro q v z
    field_simp [hw]
    ring
  exact (fullSignSpan_congr he).mp (fullSignSpan_scale (neg_ne_zero.mpr hw) hs)

/-- Normalized original gate functions, retaining all actual coefficients. -/
lemma ordered_gate_functions (d : CoefficientSystem (Fin 3)) (r : ℝ)
    (hr : 0 < r) (hw : ∀ i, d.W i ≠ 0)
    (hu0 : d.U 0+d.W 0+d.T 0=0) (ht0 : d.W 0+r*d.T 0=0)
    (ht1 : d.T 1=0) (hv1 : d.V 1+d.W 1=0) :
    (∀ q v w, starGate d r 0 q v w/(-d.W 0)=
      comparison r q v-max 0 w+normalizedH d*max 0 v) ∧
    (∀ q v w, starGate d r 1 q v w/(-d.W 1)=
      max 0 v-max 0 w+normalizedK d*max 0 q) ∧
    (∀ q v w, starGate d r 2 q v w/(-d.W 2)=
      normalizedN d r*max 0 q+normalizedM d*max 0 v+
        normalizedL d r*comparison r q v-max 0 w) := by
  refine ⟨normalized_left d r 0 (ne_of_gt hr) (hw 0) hu0 ht0,
    normalized_right d r 1 (ne_of_gt hr) (hw 1) ht1 hv1,?_⟩
  intro q v w
  rw [normalized_gate_basis d r 2 (ne_of_gt hr) (hw 2)]
  dsimp only [normalizedN,normalizedM,normalizedL]
  ring

lemma ordered_core_spans (d : CoefficientSystem (Fin 3)) (r : ℝ)
    (hr : 0 < r) (hw : ∀ i, d.W i ≠ 0)
    (hu0 : d.U 0+d.W 0+d.T 0=0) (ht0 : d.W 0+r*d.T 0=0)
    (ht1 : d.T 1=0) (hv1 : d.V 1+d.W 1=0) (hbranch : BranchNormalForm d r) :
    ∀ i, FullSignSpan r (starGate d r i) := by
  obtain ⟨h0,h1,h2⟩ := ordered_gate_functions d r hr hw hu0 ht0 ht1 hv1
  intro i
  apply fullSignSpan_unnormalize (hw i)
  fin_cases i
  · exact (fullSignSpan_congr h0).mpr (left_core_fullSignSpan hr _)
  · exact (fullSignSpan_congr h1).mpr (right_core_fullSignSpan hr _)
  · rcases hbranch with ⟨hh,hk,hn,hm,hl⟩ | ⟨hk,hh,hn,hm,hl⟩
    · have he : ∀ q v w, starGate d r 2 q v w/(-d.W 2)=
          comparison r q v-max 0 q-max 0 w+normalizedK d*max 0 q := by
        intro q v w
        rw [h2,hn,hm,hl]
        ring
      exact (fullSignSpan_congr he).mpr (branchI_negative_fullSignSpan hr _)
    · have he : ∀ q v w, starGate d r 2 q v w/(-d.W 2)=
          max 0 q+(1+normalizedH d)*max 0 v-max 0 w := by
        intro q v w
        rw [h2,hn,hm,hl]
        ring
      exact (fullSignSpan_congr he).mpr (branchII_negative_fullSignSpan hr _)

private lemma opposite_ray_contradiction {ι : Type*} [Fintype ι]
    (B C : ℝ) (w o s : ι → ℝ)
    (hB : B=∑ i,s i*w i) (hC : C=∑ i,s i*(-w i))
    (hx : 1=B+∑ i,o i*relu (w i)) (hy : 1=C+∑ i,o i*relu (-w i))
    (ho : (∑ i,o i*|w i|)=1) : False := by
  have hc : C = (-1)*B := by
    rw [hB,hC,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hs : (∑ i,o i*relu (w i))+(∑ i,o i*relu (-w i))=1 := by
    rw [← Finset.sum_add_distrib]
    simp only [← mul_add,relu_add_relu_neg_eq_abs]
    exact ho
  linarith only [hx,hy,hc,hs]

/-- The actual remainder cannot be a linear combination of the actual cores. -/
lemma ordered_remainder_not_span (d : CoefficientSystem (Fin 3)) (r : ℝ)
    (hr : 0 < r) (H : RepresentsStar d r) (hw : ∀ i,d.W i≠0)
    (hu0 : d.U 0+d.W 0+d.T 0=0) (ht0 : d.W 0+r*d.T 0=0)
    (ht1 : d.T 1=0) (hv1 : d.V 1+d.W 1=0)
    (he0 : effectiveOutput d 0=1) (he1 : effectiveOutput d 1=1)
    (he2 : effectiveOutput d 2 = -1) (hbranch : BranchNormalForm d r) :
    ¬ ∃ s : Fin 3 → ℝ, ∀ q v w, starBase d r q v w=
      ∑ i,s i*starGate d r i q v w := by
  obtain ⟨f0,f1,f2⟩ := ordered_gate_functions d r hr hw hu0 ht0 ht1 hv1
  have ho : (∑ i,d.out i*|d.W i|)=1 := by
    change (∑ i,effectiveOutput d i)=1
    norm_num [Fin.sum_univ_succ,he0,he1,he2]
  have hwRay : ∀ i,starGate d r i 0 0 1=d.W i := by
    intro i
    norm_num [starGate,starLinearForm]
  have hm : (∃ q v : ℝ, max (max 0 (q+v)) (max v (relu 0))=1 ∧
      ∀ i,starGate d r i q v 0 = -d.W i) := by
    rcases hbranch with ⟨hh,hk,hn,hM,hL⟩ | ⟨hk,hh,hn,hM,hL⟩
    · refine ⟨0,1,by norm_num [relu],?_⟩
      have hA : comparison r 0 1=1 := by
        unfold comparison
        simp only [zero_add,mul_one,max_self,mul_zero,sub_zero,max_eq_right hr.le]
        exact div_self (ne_of_gt hr)
      intro i
      have he : starGate d r i 0 1 0/(-d.W i)=1 := by
        fin_cases i
        · change starGate d r (0 : Fin 3) 0 1 0/(-d.W 0)=1
          rw [f0,hA,hh]; norm_num
        · change starGate d r (1 : Fin 3) 0 1 0/(-d.W 1)=1
          rw [f1]; norm_num
        · change starGate d r (2 : Fin 3) 0 1 0/(-d.W 2)=1
          rw [f2,hA,hn,hM,hL]; norm_num
      exact (div_eq_one_iff_eq (neg_ne_zero.mpr (hw i))).mp he
    · refine ⟨1,0,by norm_num [relu],?_⟩
      have hA : comparison r 1 0=1 := by
        unfold comparison
        norm_num
        field_simp [ne_of_gt hr]
      intro i
      have he : starGate d r i 1 0 0/(-d.W i)=1 := by
        fin_cases i
        · change starGate d r (0 : Fin 3) 1 0 0/(-d.W 0)=1
          rw [f0,hA]; norm_num
        · change starGate d r (1 : Fin 3) 1 0 0/(-d.W 1)=1
          rw [f1,hk]; norm_num
        · change starGate d r (2 : Fin 3) 1 0 0/(-d.W 2)=1
          rw [f2,hA,hn,hM,hL]; norm_num
      exact (div_eq_one_iff_eq (neg_ne_zero.mpr (hw i))).mp he
  obtain ⟨q,v,htarget,hm⟩ := hm
  rintro ⟨s,hs⟩
  have hx := H 0 0 1
  have hy := H q v 0
  simp_rw [hwRay] at hx
  simp_rw [hm] at hy
  norm_num [relu] at hx
  rw [htarget] at hy
  have hB := hs 0 0 1
  have hC := hs q v 0
  simp_rw [hwRay] at hB
  simp_rw [hm] at hC
  exact opposite_ray_contradiction _ _ d.W d.out s hB hC hx hy ho

/-- Original gate indices inherit determining sign domains and a remainder
outside their span, without assuming a physical or residual role ordering. -/
theorem three_gate_signs_and_nonspan {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0<r) (hr1 : r≤1)
    (H : RepresentsStar d r) (hcard : Fintype.card ι=3) :
    (∀ i,FullSignSpan r (starGate d r i)) ∧
      ¬ ∃ s : ι → ℝ, ∀ q v w,starBase d r q v w=∑ i,s i*starGate d r i q v w := by
  obtain ⟨e,He,hp,hq,hn,hw,hu0,ht0,ht1,hv1⟩ := exists_ordered_three d r hr hr1 H hcard
  obtain ⟨he0,he1,he2,hbranch,_⟩ :=
    ordered_three_classification (d.reindex e) r hr hr1 He hp hq hn hw hu0 ht0 ht1 hv1
  have hsp := ordered_core_spans (d.reindex e) r hr hw hu0 ht0 ht1 hv1 hbranch
  refine ⟨?_,?_⟩
  · intro i
    have hspi := hsp (e.symm i)
    change FullSignSpan r (fun q v w => starGate (d.reindex e) r (e.symm i) q v w) at hspi
    change FullSignSpan r (fun q v w => starGate d r i q v w)
    simpa only [starGate,Mixed65.ResidualSystem.reindex,Function.comp_apply,
      Equiv.apply_symm_apply] using hspi
  · rintro ⟨s,hs⟩
    apply ordered_remainder_not_span (d.reindex e) r hr He hw hu0 ht0 ht1 hv1 he0 he1 he2 hbranch
    refine ⟨s ∘ e,?_⟩
    intro q v w
    have heq : (∑ i : Fin 3,(s ∘ e) i*starGate (d.reindex e) r i q v w)=
        ∑ i : ι,s i*starGate d r i q v w := by
      exact Equiv.sum_comp e (fun i => s i*starGate d r i q v w)
    rw [heq]
    exact hs q v w
end MaxCaterpillar.Fiber.Count65.Star
