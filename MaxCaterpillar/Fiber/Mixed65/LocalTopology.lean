import MaxCaterpillar.Fiber.First65.LocalMixed
import MaxCaterpillar.Fiber.SeparationTopology

/-! # Openness of finite mixed-first-layer certificates

The certificate conditions are strict inequalities on the actual first
matrix. Their openness uses the ordinary Euclidean parameter topology,
including all suffix coefficients and biases.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open Set Frontier BigOperators

theorem continuous_first_row_lin (j : Fin 6) (x : Point 4) :
    Continuous (fun A : Fin 6 → Point 4 => lin (A j) x) := by
  unfold lin
  refine continuous_finset_sum _ fun i _ => ?_
  have hcoord : Continuous (fun A : Fin 6 → Point 4 => A j i) :=
    (continuous_apply i).comp (continuous_apply j)
  exact hcoord.mul continuous_const

theorem isOpen_inactiveOutside (x : Point 4) (J : Finset (Fin 6)) :
    IsOpen {A : Fin 6 → Point 4 | InactiveOutside A x J} := by
  simp only [InactiveOutside, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _hj
  exact isOpen_lt (continuous_first_row_lin j x) continuous_const

/-- Every field of the certificate is a strict continuous inequality. -/
theorem isOpen_localCertificate (t : ℝ) :
    IsOpen {A : Fin 6 → Point 4 | LocalCertificate t A} := by
  apply isOpen_iff_mem_nhds.mpr
  intro A hA
  have hcoord (j : Fin 6) (i : Fin 4) :
      Continuous (fun B : Fin 6 → Point 4 => B j i) :=
    (continuous_apply i).comp (continuous_apply j)
  filter_upwards
    [(isOpen_lt continuous_const (hcoord 0 0)).mem_nhds hA.q_pos,
     (isOpen_lt continuous_const (hcoord 1 1)).mem_nhds hA.b_pos,
     (isOpen_lt continuous_const (hcoord 2 3)).mem_nhds hA.c_pos,
     (isOpen_lt continuous_const (hcoord 3 0)).mem_nhds hA.t_pos,
     (isOpen_lt continuous_const (hcoord 3 2)).mem_nhds hA.t_mid_pos,
     (isOpen_lt continuous_const (hcoord 4 2)).mem_nhds hA.carrier_pos,
     (isOpen_lt (hcoord 5 2) continuous_const).mem_nhds hA.carrier_neg,
     (isOpen_inactiveOutside (carrierPlusPoint t) {4}).mem_nhds hA.carrierPlus,
     (isOpen_inactiveOutside (carrierMinusPoint t) {5}).mem_nhds hA.carrierMinus,
     (isOpen_inactiveOutside bPoint {1, 4}).mem_nhds hA.bCell,
     (isOpen_inactiveOutside (cPoint t) {2, 4}).mem_nhds hA.cCell,
     (isOpen_inactiveOutside (qPoint t) {0, 1, 4}).mem_nhds hA.qCell,
     (isOpen_inactiveOutside tPoint {0, 3, 4}).mem_nhds hA.tCell,
     (isOpen_inactiveOutside bTiePlus {1, 4}).mem_nhds hA.bTiePlusCell,
     (isOpen_inactiveOutside bTieMinus {1, 5}).mem_nhds hA.bTieMinusCell,
     (isOpen_inactiveOutside (cTiePlus t) {2, 4}).mem_nhds hA.cTiePlusCell,
     (isOpen_inactiveOutside (cTieMinus t) {2, 5}).mem_nhds hA.cTieMinusCell]
    with B hq hb hc ht ht' hp hn hcp hcn hbc hcc hqc htc hbp hbn htp htn
  exact ⟨hq, hb, hc, ht, ht', hp, hn, hcp, hcn, hbc, hcc, hqc, htc,
    hbp, hbn, htp, htn⟩

theorem isOpen_localCertificate_exactFiber (t : ℝ) :
    IsOpen {net : ExactFiber 4 6 5 | LocalCertificate t net.val.W₁} :=
  (isOpen_localCertificate t).preimage
    (continuous_W₁.comp continuous_subtype_val)

end MaxCaterpillar.Fiber.Mixed65
