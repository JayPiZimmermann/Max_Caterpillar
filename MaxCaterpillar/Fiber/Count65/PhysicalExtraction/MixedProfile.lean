import MaxCaterpillar.Fiber.Count65.Mixed.ResidualNonspan
import MaxCaterpillar.Fiber.Count65.Mixed.FunctionSpans
import MaxCaterpillar.Fiber.Mixed65.PhysicalExtraction

/-! # The actual mixed residual classification supplies the physical tail profile

This bridge quantifies over arbitrary feature-linear functions and all real
inputs. It transports the proved three-gate classification back to the
original physical gate indices; it does not assume any physical role ordering.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65
open BigOperators MaxCaterpillar.Frontier
open MaxCaterpillar.Fiber.Count65.PhysicalExtraction

/-- Every original core has both determining sign domains, regardless of its
position in the ordered residual normal form. -/
theorem ResidualSystem.original_core_sign_rigid {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (hcard : Fintype.card ι = 3) (j : ι) :
    CoreSignRigid (featureSpace t)
      (fun x : InvariantState => d.gate t j x.1 x.2.1 x.2.2) := by
  obtain ⟨e, _, _, _, _, hspans, _⟩ := d.exists_full_span_normal_form t ht h hcard
  have hs : FormBothSignSpans t (d.U j) (d.V j) (d.W j) (d.T j) := by
    have hh := hspans (e.symm j)
    simpa only [ResidualSystem.reindex, Function.comp_apply,
      Equiv.apply_symm_apply] using hh
  exact ⟨hs.exists_negative, hs.exists_positive, hs.determinesNegative,
    hs.determinesPositive⟩

/-- The remainder is not parallel to any original core. -/
theorem ResidualSystem.original_remainder_not_parallel {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (hcard : Fintype.card ι = 3) (j : ι) :
    ¬ ∃ k : ℝ, ∀ q b c : ℝ, d.base t q b c = k * d.gate t j q b c := by
  classical
  obtain ⟨e, _, _, _, _, _, hnot⟩ := d.exists_full_span_normal_form t ht h hcard
  rintro ⟨k,hk⟩
  apply hnot
  refine ⟨fun i => if i = e.symm j then k else 0, ?_⟩
  intro q b c
  have hsum : (∑ i : Fin 3, (if i = e.symm j then k else 0) *
      (d.reindex e).gate t i q b c) = k * d.gate t j q b c := by
    rw [Finset.sum_eq_single (e.symm j)]
    · simp only [if_true, ResidualSystem.gate, ResidualSystem.reindex,
        Function.comp_apply, Equiv.apply_symm_apply]
    · intro i _ hi
      rw [if_neg hi, zero_mul]
    · simp
  rw [hsum]
  exact hk q b c

/-- Any actual mixed three-core residual tail has the exact analytic profile
needed to exclude three moving physical gates. No residual chart is assumed. -/
theorem mixed_tail_profile {t : ℝ} (ht : 0 < t)
    (D I J : InvariantState → ℝ) (ε η ζ : ℝ)
    (hD : D ∈ featureSpace t) (hI : I ∈ featureSpace t) (hJ : J ∈ featureSpace t) :
    TailProfile (featureSpace t) invariantTarget D
      (fun x => η * relu (I x) + ζ * relu (J x)) ε := by
  intro R hR hrepr
  rcases hD with ⟨dU,dV,dW,dT,rfl⟩
  rcases hI with ⟨iU,iV,iW,iT,rfl⟩
  rcases hJ with ⟨jU,jV,jW,jT,rfl⟩
  rcases hR with ⟨rU,rV,rW,rT,rfl⟩
  let s : ResidualSystem (Fin 3) := {
    lU := rU, lV := rV, lW := rW, lT := rT
    out := ![ε,η,ζ]
    U := ![dU,iU,jU]
    V := ![dV,iV,jV]
    W := ![dW,iW,jW]
    T := ![dT,iT,jT] }
  have hs : s.Represents t := by
    intro q b c
    have hh := hrepr (q,b,c)
    change max (max (q+b) b) (relu c) = s.base t q b c +
      ∑ i, s.out i * relu (s.gate t i q b c)
    simp only [s, ResidualSystem.base, ResidualSystem.gate,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.head_cons, Matrix.tail_cons, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, add_zero]
    change max (max (q+b) b) (relu c) = form t rU rV rW rT q b c +
      (ε * relu (form t dU dV dW dT q b c) +
        (η * relu (form t iU iV iW iT q b c) +
          ζ * relu (form t jU jV jW jT q b c)))
    change max (max (q+b) b) (relu c) = form t rU rV rW rT q b c +
      ε * relu (form t dU dV dW dT q b c) +
        (η * relu (form t iU iV iW iT q b c) +
          ζ * relu (form t jU jV jW jT q b c)) at hh
    linarith only [hh]
  constructor
  · simpa only [s, ResidualSystem.gate, Matrix.cons_val_zero, readout]
      using s.original_core_sign_rigid t ht hs (by norm_num) 0
  · rintro ⟨k,hk⟩
    apply s.original_remainder_not_parallel t ht hs (by norm_num) 0
    refine ⟨k, ?_⟩
    intro q b c
    have hh := hk (q,b,c)
    simpa only [s, ResidualSystem.base, ResidualSystem.gate,
      Matrix.cons_val_zero, readout] using hh

#print axioms ResidualSystem.original_core_sign_rigid
#print axioms ResidualSystem.original_remainder_not_parallel
#print axioms mixed_tail_profile
end MaxCaterpillar.Fiber.Mixed65
