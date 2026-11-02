import MaxCaterpillar.Frontier.StarCertificate.Mobius
import MaxCaterpillar.Frontier.StarCertificate.MobiusCrease

/-! # A finite-fan Möbius certificate from actual chamber identities

This is the sufficient direction of Jensen's Lemma 14, with the concrete
five-coordinate normalization. The analytic hypothesis is an actual affine
identity on each positive-gap chamber, not an assumed crease cancellation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

noncomputable def weightedChainAbs (γ : Point 4) : ℝ :=
  evalForm starOmega (fun r => |γ r|)

theorem weightedChainAbs_neg (γ : Point 4) :
    weightedChainAbs (-γ)=weightedChainAbs γ := by
  simp only [weightedChainAbs,Pi.neg_apply,abs_neg]

theorem weightedChainAbs_mul (a : ℝ) (ha : 0<a) (γ : Point 4) :
    weightedChainAbs (a•γ)=a*weightedChainAbs γ := by
  unfold weightedChainAbs
  have he : (fun r => |(a•γ) r|)=fun r => a*|γ r| := by
    funext r
    simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos ha]
  rw [he,evalForm_mul_input]

theorem weightedChainAbs_zero : weightedChainAbs 0=0 := by
  simp [weightedChainAbs,evalForm]

theorem mixedCoordinates_iff_signs (γ : Point 4) :
    HasMixedCoordinates γ ↔ Mixed (coordinateSigns γ) := by
  constructor
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨⟨a,(Sign.eq_signOf (s := .neg) (a := γ a) ha).symm⟩,
      ⟨b,(Sign.eq_signOf (s := .pos) (a := γ b) hb).symm⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    have hneg := signOf_holds (γ a)
    have hpos := signOf_holds (γ b)
    change signOf (γ a)=.neg at ha
    change signOf (γ b)=.pos at hb
    rw [ha] at hneg
    rw [hb] at hpos
    exact ⟨⟨a,hneg⟩,⟨b,hpos⟩⟩

theorem nonmixed_head_agrees : ∀ (s : Fin 4→Sign), ¬Mixed s →
    ∀ i, s i=.zero ∨ headSign s=s i := by decide

theorem nonmixed_orientation_mul (γ : Point 4)
    (hm : ¬Mixed (coordinateSigns γ)) (i : Fin 4) :
    ((headSign (coordinateSigns γ)).direction : ℝ)*γ i=|γ i| := by
  have hs := signOf_holds (γ i)
  rcases nonmixed_head_agrees (coordinateSigns γ) hm i with hi | hi
  · change signOf (γ i)=.zero at hi
    rw [hi] at hs
    change γ i=0 at hs
    simp [hs]
  · rw [hi]
    change ((signOf (γ i)).direction : ℝ)*γ i=|γ i|
    cases he : signOf (γ i) <;> rw [he] at hs
    · norm_num [Sign.direction,abs_of_neg hs]
    · change γ i=0 at hs
      simp [Sign.direction,hs]
    · norm_num [Sign.direction,abs_of_pos hs]

/-- The concrete selector certificate agrees with the absolute factorial
weight on every nonmixed vector, including all coordinate-zero faces. -/
theorem starXi_nonmixed_abs (γ : Point 4) (hm : ¬HasMixedCoordinates γ) :
    starXi γ=weightedChainAbs γ := by
  have hs : ¬Mixed (coordinateSigns γ) := by
    intro hh
    exact hm ((mixedCoordinates_iff_signs γ).mpr hh)
  rw [starXi,xi_nonmixed _ _ _ _ hs]
  simp only [weightedChainAbs,evalForm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←nonmixed_orientation_mul γ hs i]
  ring

theorem starXi_even (γ : Point 4) : starXi (-γ)=starXi γ := xi_neg _ _ _ _

theorem starXi_homogeneous (a : ℝ) (ha : 0<a) (γ : Point 4) :
    starXi (a•γ)=a*starXi γ := xi_mul_pos _ _ _ _ _ ha

theorem starXi_zero : starXi 0=0 := xi_zero _ _ _

/-- Exact scalar normalization of the certificate decomposition, before
using any cancellation or any finite certificate identity. -/
theorem scaled_topMobius_relu_decomposition
    (F : Finset (Fin 5)→ℝ) (h0 : F ∅=0) (h1 : F Finset.univ=0)
    (hμ : topMobius F=0) (Ξ : Point 4→ℝ) :
    480*topMobius (fun B => relu (F B))=
      (∑ p : Fin 120, Ξ (setFunctionChain F p))+
      ∑ p : Fin 120, (weightedChainAbs (setFunctionChain F p)-Ξ (setFunctionChain F p)) := by
  have habs := sum_weighted_setFunctionChain (fun B => |F B|)
    (by change |F ∅|=0; rw [h0,abs_zero])
    (by change |F Finset.univ|=0; rw [h1,abs_zero])
  have htwice := twice_topMobius_relu F
  rw [hμ,zero_add] at htwice
  have he : (∑ p : Fin 120, weightedChainAbs (setFunctionChain F p))=
      240*topMobius (fun B => |F B|) := habs
  rw [Finset.sum_sub_distrib]
  linarith only [he,htwice]

/-- Generic certificate theorem for a finite family of actual set functions.
All four substantive hypotheses are visible: zero endpoint values, zero
unrectified top coefficient, the per-neuron certificate identity, and the
actual positive-gap affine identities. -/
theorem certificate_topMobius_zero {ι : Type*} [Fintype ι]
    (G : ι→Finset (Fin 5)→ℝ) (c : ι→ℝ) (Q : Finset (Fin 5)→ℝ)
    (Ξ : Point 4→ℝ)
    (heven : ∀ γ, Ξ (-γ)=Ξ γ)
    (hhom : ∀ a : ℝ, 0<a → ∀ γ, Ξ (a•γ)=a*Ξ γ)
    (hzero : Ξ 0=0)
    (hnonmixed : ∀ γ, ¬HasMixedCoordinates γ → Ξ γ=weightedChainAbs γ)
    (hG0 : ∀ i, G i ∅=0) (hG1 : ∀ i, G i Finset.univ=0)
    (hGμ : ∀ i, topMobius (G i)=0)
    (hcertificate : ∀ i, (∑ p : Fin 120, Ξ (setFunctionChain (G i) p))=0)
    (hchamber : ∀ p : Fin 120, ∃ l : Point 4, ∃ β : ℝ,
      ∀ x : Point 4, (∀ j, 0<x j) →
        lin l x+β=∑ i, c i*relu (lin (setFunctionChain (G i) p) x))
    (hQ : topMobius Q=0) :
    topMobius (fun B => (∑ i, c i*relu (G i B))+Q B)=0 := by
  let Λ : Point 4→ℝ := fun γ => weightedChainAbs γ-Ξ γ
  have hΛeven : ∀ γ, Λ (-γ)=Λ γ := by
    intro γ
    simp only [Λ,weightedChainAbs_neg,heven]
  have hΛhom : ∀ a : ℝ, 0<a → ∀ γ, Λ (a•γ)=a*Λ γ := by
    intro a ha γ
    dsimp only [Λ]
    rw [weightedChainAbs_mul a ha,hhom a ha]
    ring
  have hΛzero : Λ 0=0 := by simp only [Λ,weightedChainAbs_zero,hzero,sub_self]
  have hΛnonmixed : ∀ γ, ¬HasMixedCoordinates γ → Λ γ=0 := by
    intro γ hγ
    simp only [Λ,hnonmixed γ hγ,sub_self]
  have hcancel : ∀ p : Fin 120,
      (∑ i, c i*Λ (setFunctionChain (G i) p))=0 := by
    intro p
    obtain ⟨l,β,h⟩ := hchamber p
    exact positive_gap_even_functional_cancel _ c l β h Λ
      hΛeven hΛhom hΛzero hΛnonmixed
  have hscaled : (∑ i, c i*(480*topMobius (fun B => relu (G i B))))=0 := by
    simp_rw [scaled_topMobius_relu_decomposition _ (hG0 _) (hG1 _) (hGμ _) Ξ,
      hcertificate,zero_add]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun p _ => hcancel p)
  have hμsum : (∑ i, c i*topMobius (fun B => relu (G i B)))=0 := by
    have he : (∑ i, c i*(480*topMobius (fun B => relu (G i B))))=
        480*(∑ i, c i*topMobius (fun B => relu (G i B))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hscaled
    linarith only [hscaled]
  rw [topMobius_add,topMobius_sum]
  simp_rw [topMobius_mul]
  rw [hμsum,hQ,add_zero]

/-- A zero top coefficient is incompatible with the actual Boolean values
of Max5, whose top coefficient is exactly one. -/
theorem not_booleanOR_of_topMobius_zero (F : Finset (Fin 5)→ℝ)
    (h : topMobius F=0) : ¬ (∀ B, F B=booleanOR B) := by
  intro he
  have hf : F=booleanOR := funext he
  rw [hf,topMobius_booleanOR] at h
  norm_num at h

#print axioms starXi_nonmixed_abs
#print axioms certificate_topMobius_zero
#print axioms not_booleanOR_of_topMobius_zero
end MaxCaterpillar.Frontier.StarCertificate
