import MaxCaterpillar.Fiber.Count65.MatrixForms
import Mathlib.Data.List.FinRange
import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing.PairedCarriers

/-! # The paired first-matrix normal form for actual Max4 realizations

The canonical matrix is obtained only after the four opposite carrier rows
have been proved from actual-network exactness. The two finite enumerations
are genuine permutations, and all six row factors are strictly positive.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Fiber.Count65.TwoInvariantPairing
open BigOperators

/-- Convert the proved weight-row certificate to the sector's actual matrix
predicate. No statement about second-layer parameters is assumed. -/
theorem pairedFirstMatrixForm_of_certificate (net : Network 4 6 5)
    (fr : TwoInvariantAnchorFrame net) (P : PairedCarrierCertificate net fr) :
    PairedFirstMatrixForm net := by
  classical
  let f : Fin 6 → Fin 6 := ![fr.firstRoot,fr.secondRoot,P.j,P.k,P.l,P.m]
  let g : Fin 4 → Fin 4 := ![fr.p,fr.q,fr.r,fr.s]
  have hz₁ : (∑ i, net.W₁ fr.firstRoot i) = 0 := by
    have hm : fr.firstRoot ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0 := by
      rw [fr.invariant_rows]
      simp
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hm
  have hz₂ : (∑ i, net.W₁ fr.secondRoot i) = 0 := by
    have hm : fr.secondRoot ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0 := by
      rw [fr.invariant_rows]
      simp
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hm
  have root_ne (r t : Fin 6) (hr : (∑ i, net.W₁ r i) = 0)
      (ht : (∑ i, net.W₁ t i) ≠ 0) : r ≠ t := by
    intro he
    exact ht (he ▸ hr)
  have h01 := fr.roots_ne
  have h02 := root_ne _ _ hz₁ P.j_carrier
  have h03 := root_ne _ _ hz₁ P.k_carrier
  have h04 := root_ne _ _ hz₁ P.l_carrier
  have h05 := root_ne _ _ hz₁ P.m_carrier
  have h12 := root_ne _ _ hz₂ P.j_carrier
  have h13 := root_ne _ _ hz₂ P.k_carrier
  have h14 := root_ne _ _ hz₂ P.l_carrier
  have h15 := root_ne _ _ hz₂ P.m_carrier
  have h23 := P.jk_ne
  have h24 := P.jl_ne
  have h25 := P.jm_ne
  have h34 := P.kl_ne
  have h35 := P.km_ne
  have h45 := P.lm_ne
  have hf : Function.Injective f := by
    apply (List.nodup_ofFn (f := f)).mp
    simp [f,List.ofFn_succ,Matrix.cons_val_succ',
      h01,h02,h03,h04,h05,h12,h13,h14,h15,h23,h24,h25,h34,h35,h45]
  have hpq := fr.pq_ne
  have hpr := fr.pr_ne
  have hps := fr.ps_ne
  have hqr := fr.qr_ne
  have hqs := fr.qs_ne
  have hrs := fr.rs_ne
  have hg : Function.Injective g := by
    apply (List.nodup_ofFn (f := g)).mp
    simp [g,List.ofFn_succ,Matrix.cons_val_succ',hpq,hpr,hps,hqr,hqs,hrs]
  let eRows : Equiv.Perm (Fin 6) :=
    Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  let eInput : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩
  let A : ℝ := net.W₁ P.j fr.q
  let B : ℝ := net.W₁ P.j fr.s
  let C : ℝ := net.W₁ P.l fr.q
  let D : ℝ := net.W₁ P.l fr.s
  let scale : Fin 6 → ℝ :=
    ![fr.firstScale,fr.secondScale,1,-P.firstRatio,1,-P.secondRatio]
  have hscale : ∀ j, 0 < scale j := by
    intro j
    fin_cases j
    · simpa [scale] using fr.firstScale_pos
    · simpa [scale] using fr.secondScale_pos
    · norm_num [scale]
    · simpa [scale, Matrix.cons_val_succ'] using neg_pos.mpr P.firstRatio_neg
    · norm_num [scale, Matrix.cons_val_succ']
    · simpa [scale, Matrix.cons_val_succ'] using neg_pos.mpr P.secondRatio_neg
  have hjp : net.W₁ P.j fr.p = 0 :=
    fr.carrier_plane P.j P.j_carrier fr.p fr.pq_ne fr.ps_ne
  have hjr : net.W₁ P.j fr.r = 0 :=
    fr.carrier_plane P.j P.j_carrier fr.r fr.qr_ne.symm fr.rs_ne
  have hlp : net.W₁ P.l fr.p = 0 :=
    fr.carrier_plane P.l P.l_carrier fr.p fr.pq_ne fr.ps_ne
  have hlr : net.W₁ P.l fr.r = 0 :=
    fr.carrier_plane P.l P.l_carrier fr.r fr.qr_ne.symm fr.rs_ne
  have hmatrix : ∀ j i, net.W₁ (f j) (g i) = scale j * pairedRows A B C D j i := by
    intro j i
    fin_cases j <;> fin_cases i <;>
      simp [f,g,scale,pairedRows,A,B,C,D,Matrix.cons_val_succ',
        fr.first_form,fr.second_form,P.first_pair,P.second_pair,hjp,hjr,hlp,hlr,
        fr.pq_ne,fr.pr_ne,fr.ps_ne,fr.qr_ne,fr.qs_ne,fr.rs_ne,
        fr.pq_ne.symm,fr.pr_ne.symm,fr.ps_ne.symm,fr.qr_ne.symm,
        fr.qs_ne.symm,fr.rs_ne.symm] <;> ring
  refine ⟨A,B,C,D,P.independent,fun j => scale (eRows.symm j),
    fun j => hscale (eRows.symm j),eRows.symm,eInput.symm,?_⟩
  intro j i
  have hj : f (eRows.symm j) = j := eRows.apply_symm_apply j
  have hi : g (eInput.symm i) = i := eInput.apply_symm_apply i
  simpa only [hj,hi] using hmatrix (eRows.symm j) (eInput.symm i)

/-- The sector's genuine first-matrix condition follows from actual global
Max4 exactness and exactly two invariant first rows. Biases are arbitrary. -/
theorem pairedFirstMatrixForm_of_two_invariant (net : Network 4 6 5)
    (hexact : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 2) :
    PairedFirstMatrixForm net := by
  obtain ⟨fr,⟨P⟩⟩ := max4_two_invariant_paired_carriers net hexact hcard
  exact pairedFirstMatrixForm_of_certificate net fr P

#check @pairedFirstMatrixForm_of_two_invariant
#print axioms pairedFirstMatrixForm_of_two_invariant
end MaxCaterpillar.Fiber.Count65.TwoInvariantPairing
