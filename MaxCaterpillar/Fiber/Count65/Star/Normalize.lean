import MaxCaterpillar.Fiber.Count65.Star.Ordering
import MaxCaterpillar.Fiber.Count65.Star.FeatureSpace
import MaxCaterpillar.Fiber.Count65.Star.ResidualClassification

/-! # Normalizing the original three star residual gates

All divisions use coefficients already proved nonzero by carrier forcing.
Orientation reversal adds the actual feature-linear gate to the remainder.
No gate is discarded or replaced by an independent residual witness.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.Star
open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65

lemma weighted_fold_normalize (o w g : ℝ) (hw : w ≠ 0) :
    o * relu g = (o * |w|) * relu (g / (-w)) + (if 0 < w then o * g else 0) := by
  rcases lt_or_gt_of_ne hw with hn | hp
  · have he : (-w) * (g / (-w)) = g := by field_simp [hw]; ring
    have hf := relu_mul_pos (neg_pos.mpr hn) (g / (-w))
    rw [he] at hf
    rw [abs_of_neg hn, if_neg (not_lt.mpr hn.le), add_zero, hf]
    ring
  · have he : w * (g / (-w)) = -g := by field_simp [hw]; ring
    have hf := relu_mul_pos hp (g / (-w))
    rw [he] at hf
    rw [abs_of_pos hp, if_pos hp]
    linarith only [congrArg (fun z : ℝ => o * z) hf,
      congrArg (fun z : ℝ => o * z) (relu_sub_relu_neg g)]

lemma normalized_gate_basis {ι : Type*} (d : CoefficientSystem ι)
    (r : ℝ) (i : ι) (hr : r ≠ 0) (hw : d.W i ≠ 0) (q v w : ℝ) :
    starGate d r i q v w / (-d.W i) =
      ((d.U i + (1-r)*d.T i) / (-d.W i)) * max 0 q +
      (d.V i / (-d.W i)) * max 0 v - max 0 w +
      ((r*d.T i) / (-d.W i)) * comparison r q v := by
  unfold starGate starLinearForm comparison
  field_simp [hr,hw]
  ring

lemma normalized_left {ι : Type*} (d : CoefficientSystem ι) (r : ℝ) (i : ι)
    (hr : r ≠ 0) (hw : d.W i ≠ 0)
    (hu : d.U i + d.W i + d.T i = 0) (ht : d.W i + r*d.T i = 0)
    (q v w : ℝ) :
    starGate d r i q v w / (-d.W i) =
      comparison r q v - max 0 w + (d.V i / (-d.W i)) * max 0 v := by
  have hn : d.U i + (1-r)*d.T i = 0 := by nlinarith only [hu,ht]
  have hrt : r*d.T i = -d.W i := by linarith only [ht]
  rw [normalized_gate_basis d r i hr hw,hn,hrt,zero_div,zero_mul,
    div_self (neg_ne_zero.mpr hw),one_mul,zero_add]
  ring

lemma normalized_right {ι : Type*} (d : CoefficientSystem ι) (r : ℝ) (i : ι)
    (hr : r ≠ 0) (hw : d.W i ≠ 0)
    (ht : d.T i = 0) (hv : d.V i + d.W i = 0) (q v w : ℝ) :
    starGate d r i q v w / (-d.W i) =
      max 0 v - max 0 w + (d.U i / (-d.W i)) * max 0 q := by
  have hv' : d.V i = -d.W i := by linarith only [hv]
  simp only [normalized_gate_basis d r i hr hw,ht,hv',mul_zero,add_zero,zero_div,zero_mul,
    div_self (neg_ne_zero.mpr hw),one_mul,add_zero]
  ring

noncomputable def correctedBase (d : CoefficientSystem (Fin 3)) (r : ℝ)
    (x : InvariantState) : ℝ :=
  starBase d r x.1 x.2.1 x.2.2 +
    ∑ i : Fin 3, if 0 < d.W i then d.out i * starGate d r i x.1 x.2.1 x.2.2 else 0

lemma correctedBase_mem (d : CoefficientSystem (Fin 3)) (r : ℝ) :
    correctedBase d r ∈ featureSpace r := by
  classical
  have hb : (fun x : InvariantState => starBase d r x.1 x.2.1 x.2.2) ∈ featureSpace r :=
    readout_mem_featureSpace r _ _ _ _
  have ht : ∀ i : Fin 3,
      (fun x : InvariantState => if 0 < d.W i then
        d.out i * starGate d r i x.1 x.2.1 x.2.2 else 0) ∈ featureSpace r := by
    intro i
    by_cases hw : 0 < d.W i
    · simp only [if_pos hw]
      exact (featureSpace r).smul_mem (d.out i) (readout_mem_featureSpace r _ _ _ _)
    · simp only [if_neg hw]
      exact (featureSpace r).zero_mem
  have hs := (featureSpace r).sum_mem (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => ht i)
  convert (featureSpace r).add_mem hb hs using 1

noncomputable def effectiveOutput (d : CoefficientSystem (Fin 3)) (i : Fin 3) : ℝ :=
  d.out i * |d.W i|
noncomputable def normalizedH (d : CoefficientSystem (Fin 3)) : ℝ := d.V 0 / (-d.W 0)
noncomputable def normalizedK (d : CoefficientSystem (Fin 3)) : ℝ := d.U 1 / (-d.W 1)
noncomputable def normalizedN (d : CoefficientSystem (Fin 3)) (r : ℝ) : ℝ :=
  (d.U 2 + (1-r)*d.T 2) / (-d.W 2)
noncomputable def normalizedM (d : CoefficientSystem (Fin 3)) : ℝ := d.V 2 / (-d.W 2)
noncomputable def normalizedL (d : CoefficientSystem (Fin 3)) (r : ℝ) : ℝ :=
  (r*d.T 2) / (-d.W 2)

/-- Every ordered actual three-gate identity yields the normalized all-input
identity, with exact effective amplitudes and actual orientation corrections. -/
theorem ordered_normalized_identity (d : CoefficientSystem (Fin 3)) (r : ℝ)
    (hr : 0 < r) (H : RepresentsStar d r) (hw : ∀ i, d.W i ≠ 0)
    (hu0 : d.U 0 + d.W 0 + d.T 0 = 0) (ht0 : d.W 0 + r*d.T 0 = 0)
    (ht1 : d.T 1 = 0) (hv1 : d.V 1 + d.W 1 = 0) :
    ∃ eU eV eW eA : ℝ,
      NormalizedIdentity r (effectiveOutput d 0) (effectiveOutput d 1)
        (-effectiveOutput d 2) (normalizedH d) (normalizedK d)
        (normalizedN d r) (normalizedM d) (normalizedL d r) eU eV eW eA ∧
      ∀ q v w : ℝ, correctedBase d r (q,v,w) =
        eU*max 0 q+eV*max 0 v+eW*max 0 w+eA*comparison r q v := by
  classical
  obtain ⟨A,B,C,D,hR⟩ := correctedBase_mem d r
  have hre : ∀ q v w : ℝ, correctedBase d r (q,v,w) =
      (A+(1-r)*D)*max 0 q + B*max 0 v + C*max 0 w +
        (r*D)*comparison r q v := by
    intro q v w
    rw [hR]
    dsimp only [readout,starLinearForm,comparison]
    field_simp [ne_of_gt hr]
    ring
  refine ⟨A+(1-r)*D,B,C,r*D,?_,hre⟩
  intro q v w
  have f0 := weighted_fold_normalize (d.out 0) (d.W 0) (starGate d r 0 q v w) (hw 0)
  have f1 := weighted_fold_normalize (d.out 1) (d.W 1) (starGate d r 1 q v w) (hw 1)
  have f2 := weighted_fold_normalize (d.out 2) (d.W 2) (starGate d r 2 q v w) (hw 2)
  rw [normalized_left d r 0 (ne_of_gt hr) (hw 0) hu0 ht0] at f0
  rw [normalized_right d r 1 (ne_of_gt hr) (hw 1) ht1 hv1] at f1
  rw [normalized_gate_basis d r 2 (ne_of_gt hr) (hw 2)] at f2
  have hn : ((d.U 2 + (1-r)*d.T 2)/(-d.W 2))*max 0 q +
      (d.V 2/(-d.W 2))*max 0 v-max 0 w+
      ((r*d.T 2)/(-d.W 2))*comparison r q v =
      normalizedN d r*max 0 q+normalizedM d*max 0 v+
        normalizedL d r*comparison r q v-max 0 w := by
    dsimp only [normalizedN,normalizedM,normalizedL]
    ring
  rw [hn] at f2
  have hsum := H q v w
  have htgt : max (max 0 (q+v)) (max v (relu w)) = target q v w := by
    unfold target relu
    ac_rfl
  rw [htgt] at hsum
  change _ = target q v w
  rw [← hre q v w]
  dsimp only [correctedBase] at *
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at hsum ⊢
  dsimp only [effectiveOutput,normalizedH,normalizedK]
  simp only [relu] at hsum f0 f1 f2
  simp only [Fin.succ_zero_eq_one,show (Fin.succ 1 : Fin 3)=2 from rfl,add_zero] at hsum ⊢
  linarith only [hsum,f0,f1,f2]

/-- The two actual normalized coefficient branches of an ordered system. -/
def BranchNormalForm (d : CoefficientSystem (Fin 3)) (r : ℝ) : Prop :=
  (normalizedH d=0 ∧ normalizedK d≤0 ∧ normalizedN d r=normalizedK d-1 ∧
    normalizedM d=0 ∧ normalizedL d r=1) ∨
  (normalizedK d=1 ∧ normalizedH d≤-1 ∧ normalizedN d r=1 ∧
    normalizedM d=1+normalizedH d ∧ normalizedL d r=0)

/-- Full coefficient classification of the original ordered gates. The
orientation-corrected remainder is exactly the independent feature `W`. -/
theorem ordered_three_classification (d : CoefficientSystem (Fin 3)) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (H : RepresentsStar d r)
    (hp : 0 < d.out 0) (hq : 0 < d.out 1) (hn : d.out 2 < 0)
    (hw : ∀ i, d.W i ≠ 0)
    (hu0 : d.U 0+d.W 0+d.T 0=0) (ht0 : d.W 0+r*d.T 0=0)
    (ht1 : d.T 1=0) (hv1 : d.V 1+d.W 1=0) :
    effectiveOutput d 0=1 ∧ effectiveOutput d 1=1 ∧ effectiveOutput d 2 = -1 ∧
      BranchNormalForm d r ∧ ∀ q v w : ℝ, correctedBase d r (q,v,w)=max 0 w := by
  obtain ⟨eU,eV,eW,eA,Hnorm,Hbase⟩ :=
    ordered_normalized_identity d r hr H hw hu0 ht0 ht1 hv1
  have ha : 0 < effectiveOutput d 0 := mul_pos hp (abs_pos.mpr (hw 0))
  have hb : 0 < effectiveOutput d 1 := mul_pos hq (abs_pos.mpr (hw 1))
  have hg : 0 < -effectiveOutput d 2 :=
    neg_pos.mpr (mul_neg_of_neg_of_pos hn (abs_pos.mpr (hw 2)))
  obtain ⟨he,Hdata⟩ := (normalized_identity_iff hr hr1 ha hb hg).mp Hnorm
  have hbase : ∀ q v w : ℝ, correctedBase d r (q,v,w)=max 0 w := by
    intro q v w
    simpa only [he.1,he.2.1,he.2.2.1,he.2.2.2,zero_mul,one_mul,
      zero_add,add_zero] using Hbase q v w
  rcases Hdata with ⟨hh,ha1,hb1,hg1,hn1,hm,hl,hk⟩ |
    ⟨hk,ha1,hb1,hg1,hn1,hm,hl,hh⟩
  · exact ⟨ha1,hb1,by linarith only [hg1],Or.inl ⟨hh,hk,hn1,hm,hl⟩,hbase⟩
  · exact ⟨ha1,hb1,by linarith only [hg1],Or.inr ⟨hk,hh,hn1,hm,hl⟩,hbase⟩

/-- Every arbitrary real three-gate star residual has one of the two complete
coefficient normal forms after reindexing its original gates. No carrier
normalization is an input hypothesis of this theorem. -/
theorem three_gate_classification {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (H : RepresentsStar d r) (hcard : Fintype.card ι=3) :
    ∃ e : Fin 3 ≃ ι,
      RepresentsStar (d.reindex e) r ∧
      (∀ j, (d.reindex e).W j ≠ 0) ∧
      effectiveOutput (d.reindex e) 0=1 ∧ effectiveOutput (d.reindex e) 1=1 ∧
      effectiveOutput (d.reindex e) 2 = -1 ∧ BranchNormalForm (d.reindex e) r ∧
      ∀ q v w : ℝ, correctedBase (d.reindex e) r (q,v,w)=max 0 w := by
  obtain ⟨e,He,hp,hq,hn,hw,hu0,ht0,ht1,hv1⟩ := exists_ordered_three d r hr hr1 H hcard
  have hclass := ordered_three_classification (d.reindex e) r hr hr1 He hp hq hn
    hw hu0 ht0 ht1 hv1
  exact ⟨e,He,hw,hclass⟩

end MaxCaterpillar.Fiber.Count65.Star
