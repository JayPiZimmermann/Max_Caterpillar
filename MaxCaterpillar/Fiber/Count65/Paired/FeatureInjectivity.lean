import MaxCaterpillar.Fiber.Count65.Paired.PhysicalCarrier
import MaxCaterpillar.Fiber.Count65.Paired.CodeOffsets

/-! # Coefficient uniqueness over an invertible paired first dictionary

The six physical features can each be isolated by an actual real network
input. Consequently equality of two second preactivations implies equality
of their actual incoming rows. This is the model bridge needed before using
physical proportional-row or duplicate-gate paths.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open Frontier

private def featureValue (w : Fin 6 → ℝ) (q r u v : ℝ) : ℝ :=
  w 0*q+w 1*r+w 2*relu u+w 3*relu (-u)+w 4*relu v+w 5*relu (-v)

lemma paired_preact_code_probe (U R : Fin 2 → Fin 2 → ℝ)
    (hUR : CodeRightInverse U R) (w : Fin 6 → ℝ) (q r u v : ℝ)
    (hq : 0≤q) (hr : 0≤r) :
    Absorption.preact (pairedRows U) 0 w 0
      ![R 0 0*u+R 0 1*v+q,R 0 0*u+R 0 1*v,
        R 1 0*u+R 1 1*v+r,R 1 0*u+R 1 1*v] =
      w 0*q+w 1*r+w 2*relu u+w 3*relu (-u)+w 4*relu v+w 5*relu (-v) := by
  rw [paired_physical_preact]
  change codeIntercept (fun _ : Fin 1 => w) U (R 0 0*u+R 0 1*v)
      (R 1 0*u+R 1 1*v) 0+
    w 0*relu ((R 0 0*u+R 0 1*v+q)-(R 0 0*u+R 0 1*v))+
    w 1*relu ((R 1 0*u+R 1 1*v+r)-(R 1 0*u+R 1 1*v)) = _
  rw [show (R 0 0*u+R 0 1*v+q)-(R 0 0*u+R 0 1*v)=q by ring,
    show (R 1 0*u+R 1 1*v+r)-(R 1 0*u+R 1 1*v)=r by ring,
    relu_of_nonneg hq,relu_of_nonneg hr]
  have hUV := code_rightInverse_eval U R hUR u v
  simp only [codeIntercept,hUV.1,hUV.2]
  ring

/-- There are no silent recodings of a physical second row over this fixed
first hidden layer: equality on every real input determines every coefficient. -/
theorem paired_feature_injective (U R : Fin 2 → Fin 2 → ℝ)
    (hUR : CodeRightInverse U R) (w z : Fin 6 → ℝ)
    (h : ∀ x, Absorption.preact (pairedRows U) 0 w 0 x =
      Absorption.preact (pairedRows U) 0 z 0 x) : w=z := by
  have hh : ∀ q r u v : ℝ, 0≤q → 0≤r →
      featureValue w q r u v=featureValue z q r u v := by
    intro q r u v hq hr
    have he := h ![R 0 0*u+R 0 1*v+q,R 0 0*u+R 0 1*v,
      R 1 0*u+R 1 1*v+r,R 1 0*u+R 1 1*v]
    rw [paired_preact_code_probe U R hUR w q r u v hq hr,
      paired_preact_code_probe U R hUR z q r u v hq hr] at he
    exact he
  have h0 := hh 1 0 0 0 (by norm_num) (by norm_num)
  have h1 := hh 0 1 0 0 (by norm_num) (by norm_num)
  have h2 := hh 0 0 1 0 (by norm_num) (by norm_num)
  have h3 := hh 0 0 (-1) 0 (by norm_num) (by norm_num)
  have h4 := hh 0 0 0 1 (by norm_num) (by norm_num)
  have h5 := hh 0 0 0 (-1) (by norm_num) (by norm_num)
  norm_num [featureValue,relu] at h0 h1 h2 h3 h4 h5
  funext j
  fin_cases j <;> assumption

end MaxCaterpillar.Fiber.Count65.Paired
