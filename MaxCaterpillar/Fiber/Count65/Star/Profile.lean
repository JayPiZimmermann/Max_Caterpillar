import MaxCaterpillar.Fiber.Count65.Star.FunctionSpans
import MaxCaterpillar.Fiber.Count65.Star.PhysicalBridge

/-! # The full star residual supplies the actual physical tail profile -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star
open BigOperators MaxCaterpillar.Frontier
open MaxCaterpillar.Fiber.Count65.PhysicalExtraction

/-- Every unchanged original core has both determining, inhabited sign domains. -/
theorem original_core_sign_rigid {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0<r) (hr1 : r≤1)
    (H : RepresentsStar d r) (hcard : Fintype.card ι=3) (j : ι) :
    CoreSignRigid (featureSpace r)
      (fun x : InvariantState => starGate d r j x.1 x.2.1 x.2.2) :=
  ((three_gate_signs_and_nonspan d r hr hr1 H hcard).1 j).coreSignRigid

/-- The original feature-linear remainder is not parallel to any original core. -/
theorem original_remainder_not_parallel {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0<r) (hr1 : r≤1)
    (H : RepresentsStar d r) (hcard : Fintype.card ι=3) (j : ι) :
    ¬ ∃ k : ℝ, ∀ q v w, starBase d r q v w=k*starGate d r j q v w := by
  classical
  rintro ⟨k,hk⟩
  apply (three_gate_signs_and_nonspan d r hr hr1 H hcard).2
  refine ⟨fun i => if i=j then k else 0,?_⟩
  intro q v w
  rw [Finset.sum_eq_single j]
  · simpa only [if_true] using hk q v w
  · intro i _ hi
    simp only [if_neg hi,zero_mul]
  · simp

/-- Arbitrary feature-linear tails and all real output coefficients are covered.
No physical role ordering or chosen residual normal form is assumed. -/
theorem star_tail_profile {r : ℝ} (hr : 0<r) (hr1 : r≤1)
    (D I J : InvariantState → ℝ) (ε η ζ : ℝ)
    (hD : D ∈ featureSpace r) (hI : I ∈ featureSpace r) (hJ : J ∈ featureSpace r) :
    TailProfile (featureSpace r) invariantTarget D
      (fun x => η*relu (I x)+ζ*relu (J x)) ε := by
  intro R hR hrepr
  obtain ⟨dU,dV,dW,dT,rfl⟩ := hD
  obtain ⟨iU,iV,iW,iT,rfl⟩ := hI
  obtain ⟨jU,jV,jW,jT,rfl⟩ := hJ
  obtain ⟨rU,rV,rW,rT,rfl⟩ := hR
  let s : CoefficientSystem (Fin 3) := {
    lU := rU, lV := rV, lW := rW, lT := rT
    out := ![ε,η,ζ], U := ![dU,iU,jU], V := ![dV,iV,jV]
    W := ![dW,iW,jW], T := ![dT,iT,jT] }
  have hs : RepresentsStar s r := by
    intro q v w
    have hh := hrepr (q,v,w)
    have he : max (max 0 (q+v)) (max v (relu w))=invariantTarget (q,v,w) := by
      change max (max 0 (q+v)) (max v (max 0 w))=
        max (max (q+v) v) (max 0 w)
      ac_rfl
    rw [he]
    simp only [starBase,starGate,s,Fin.sum_univ_succ,Fin.sum_univ_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',
      Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two,add_zero]
    change _ = _ at hh
    dsimp only [readout] at hh
    linarith only [hh]
  constructor
  · simpa only [s,starGate,Matrix.cons_val_zero,readout] using
      original_core_sign_rigid s r hr hr1 hs (by norm_num) 0
  · rintro ⟨k,hk⟩
    apply original_remainder_not_parallel s r hr hr1 hs (by norm_num) 0
    refine ⟨k,?_⟩
    intro q v w
    have hh := hk (q,v,w)
    simpa only [s,starBase,starGate,Matrix.cons_val_zero,readout] using hh
end MaxCaterpillar.Fiber.Count65.Star
