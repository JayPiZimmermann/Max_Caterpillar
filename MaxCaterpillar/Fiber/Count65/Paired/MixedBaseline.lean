import MaxCaterpillar.Fiber.Count65.Paired.MixedTwoGate
import MaxCaterpillar.Fiber.Count65.Paired.PhysicalCarrier

/-! # Classify the two actual baseline gates in the exceptional switching cases

Opposite signs of the two target increment coefficients force one globally
uniform signed/split branch. All statements concern actual preactivations of
the unchanged physical first hidden layer, on every real input.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open Frontier Absorption

lemma two_relu_readout_opposite_signs {X : Type*} (P Q L : X→ℝ) (d e : ℝ)
    (h : ∀ x, d*relu (P x)+e*relu (Q x)=L x)
    (hp : ∃ x, 0<L x) (hn : ∃ x, L x<0) :
    (0<d ∧ e<0) ∨ (d<0 ∧ 0<e) := by
  have hpos : 0<d ∨ 0<e := by
    by_contra hh
    push_neg at hh
    obtain ⟨x,hx⟩ := hp
    have he := h x
    have hdP := mul_nonpos_of_nonpos_of_nonneg hh.1 (relu_nonneg (P x))
    have heQ := mul_nonpos_of_nonpos_of_nonneg hh.2 (relu_nonneg (Q x))
    linarith only [he,hdP,heQ,hx]
  have hneg : d<0 ∨ e<0 := by
    by_contra hh
    push_neg at hh
    obtain ⟨x,hx⟩ := hn
    have he := h x
    have hdP := mul_nonneg hh.1 (relu_nonneg (P x))
    have heQ := mul_nonneg hh.2 (relu_nonneg (Q x))
    linarith only [he,hdP,heQ,hx]
  rcases hpos with hd | he
  · rcases hneg with hn | hn
    · linarith only [hd,hn]
    · exact Or.inl ⟨hd,hn⟩
  · rcases hneg with hn | hn
    · exact Or.inr ⟨hn,he⟩
    · linarith only [he,hn]

lemma paired_preact_increment_probe (U : Fin 2 → Fin 2 → ℝ) (w : Fin 6 → ℝ)
    (a b q r : ℝ) (hq : 0≤q) (hr : 0≤r) :
    preact (pairedRows U) 0 w 0 ![a+q,a,b+r,b]=
      codeIntercept (fun _ : Fin 1 => w) U a b 0+w 0*q+w 1*r := by
  rw [paired_physical_preact]
  change codeIntercept (fun _ : Fin 1 => w) U a b 0+
    w 0*relu ((a+q)-a)+w 1*relu ((b+r)-b)=_
  rw [show (a+q)-a=q by ring,show (b+r)-b=r by ring,
    relu_of_nonneg hq,relu_of_nonneg hr]

/-- Actual normalized readout gates, with arbitrary real incoming rows, are
one signed pair or one globally nonnegative split pair. -/
theorem paired_mixed_baseline_classification (U : Fin 2 → Fin 2 → ℝ)
    (P Q L : Fin 6 → ℝ)
    (hop : (0<L 0 ∧ L 1<0) ∨ (L 0<0 ∧ 0<L 1))
    (h : ∀ x, relu (preact (pairedRows U) 0 P 0 x)-
      relu (preact (pairedRows U) 0 Q 0 x)=preact (pairedRows U) 0 L 0 x) :
    (∀ x, preact (pairedRows U) 0 P 0 x=preact (pairedRows U) 0 L 0 x ∧
      preact (pairedRows U) 0 Q 0 x= -preact (pairedRows U) 0 L 0 x) ∨
    (∀ x, 0≤preact (pairedRows U) 0 P 0 x ∧ 0≤preact (pairedRows U) 0 Q 0 x ∧
      preact (pairedRows U) 0 P 0 x-preact (pairedRows U) 0 Q 0 x=
        preact (pairedRows U) 0 L 0 x) := by
  let CP := fun z : ℝ×ℝ => codeIntercept (fun _ : Fin 1 => P) U z.1 z.2 0
  let CQ := fun z : ℝ×ℝ => codeIntercept (fun _ : Fin 1 => Q) U z.1 z.2 0
  let CL := fun z : ℝ×ℝ => codeIntercept (fun _ : Fin 1 => L) U z.1 z.2 0
  have heq : ∀ z : ℝ×ℝ, ∀ q r : ℝ, 0≤q → 0≤r →
      relu (CP z+P 0*q+P 1*r)-relu (CQ z+Q 0*q+Q 1*r)=CL z+L 0*q+L 1*r := by
    intro z q r hq hr
    have hh := h ![z.1+q,z.1,z.2+r,z.2]
    simpa only [paired_preact_increment_probe U P z.1 z.2 q r hq hr,
      paired_preact_increment_probe U Q z.1 z.2 q r hq hr,
      paired_preact_increment_probe U L z.1 z.2 q r hq hr] using hh
  have hc : (∀ z q r, 0≤q → 0≤r →
        CP z+P 0*q+P 1*r=CL z+L 0*q+L 1*r ∧
          CQ z+Q 0*q+Q 1*r= -(CL z+L 0*q+L 1*r)) ∨
      (∀ z q r, 0≤q → 0≤r → 0≤CP z+P 0*q+P 1*r ∧ 0≤CQ z+Q 0*q+Q 1*r ∧
        (CP z+P 0*q+P 1*r)-(CQ z+Q 0*q+Q 1*r)=CL z+L 0*q+L 1*r) := by
    rcases hop with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · exact mixed_two_gate_uniform CP CQ CL (P 0) (P 1) (Q 0) (Q 1) (L 0) (L 1) h0 h1 heq
    · exact mixed_two_gate_uniform_negative_first CP CQ CL (P 0) (P 1) (Q 0) (Q 1)
        (L 0) (L 1) h0 h1 heq
  rcases hc with hc | hc
  · refine Or.inl (fun x => ?_)
    have hh := hc (x 1,x 3) (relu (x 0-x 1)) (relu (x 2-x 3)) (relu_nonneg _) (relu_nonneg _)
    simpa only [paired_physical_preact] using hh
  · refine Or.inr (fun x => ?_)
    have hh := hc (x 1,x 3) (relu (x 0-x 1)) (relu (x 2-x 3)) (relu_nonneg _) (relu_nonneg _)
    simpa only [paired_physical_preact] using hh

end MaxCaterpillar.Fiber.Count65.Paired
