import MaxCaterpillar.Fiber.Count65.FrameTransport.CarrierCompletion
import MaxCaterpillar.Fiber.Count65.FourFeatures
import MaxCaterpillar.Fiber.Symmetry

/-! # Completing the invariant-frame normalization to all six physical rows

An actual four-row invariant enumeration, positive feature scales, and one
strictly inactive canonical input suffice. The two coordinate carriers and
the permutation of every actual first neuron are derived in the conclusion.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators

noncomputable def completedRows (A : Fin 4 → Point 4) (i : Fin 4) : Fin 6 → Point 4 :=
  Fin.append A ![unitVec i,-unitVec i]

/-- Appending the two actual complementary rows gives a genuine permutation
of all six row indices; no first neuron is lost or repeated. -/
theorem invariant_carrier_enumeration_bijective (net : Network 4 6 5)
    (e : Fin 4 ≃ invariantRows net) (p n : Fin 6) (hpn : p ≠ n)
    (hother : ∀ j, (∑ k, net.W₁ j k) = 0 ↔ j ≠ p ∧ j ≠ n) :
    Function.Bijective (Fin.append (fun j => (e j).val) ![p,n] : Fin 6 → Fin 6) := by
  classical
  let f : Fin 6 → Fin 6 := Fin.append (fun j => (e j).val) ![p,n]
  have hezero (j : Fin 4) : (∑ k, net.W₁ (e j).val k) = 0 :=
    (Finset.mem_filter.mp (e j).property).2
  have hinj : Function.Injective f := by
    intro a b
    refine Fin.addCases (m := 4) (n := 2)
      (motive := fun a : Fin 6 => f a = f b → a = b) (fun a => ?_) (fun a => ?_) a
    · refine Fin.addCases (m := 4) (n := 2)
        (motive := fun b : Fin 6 => f (Fin.castAdd 2 a) = f b → Fin.castAdd 2 a = b)
        (fun b => ?_) (fun b => ?_) b
      · intro hab
        simp only [f,Fin.append_left] at hab
        exact congrArg (Fin.castAdd 2) (e.injective (Subtype.ext hab))
      · intro hab
        simp only [f,Fin.append_left,Fin.append_right] at hab
        fin_cases b
        · exact False.elim (((hother _).mp (hezero a)).1 hab)
        · exact False.elim (((hother _).mp (hezero a)).2 hab)
    · refine Fin.addCases (m := 4) (n := 2)
        (motive := fun b : Fin 6 => f (Fin.natAdd 4 a) = f b → Fin.natAdd 4 a = b)
        (fun b => ?_) (fun b => ?_) b
      · intro hab
        simp only [f,Fin.append_left,Fin.append_right] at hab
        fin_cases a
        · exact False.elim (((hother _).mp (hezero b)).1 hab.symm)
        · exact False.elim (((hother _).mp (hezero b)).2 hab.symm)
      · intro hab
        simp only [f,Fin.append_right] at hab
        fin_cases a <;> fin_cases b
        · rfl
        · exact False.elim (hpn hab)
        · exact False.elim (hpn hab.symm)
        · rfl
  exact ⟨hinj,Finite.surjective_of_injective hinj⟩

/-- A reusable assembly helper: the displayed carrier equations suffice to
extend a normalized invariant dictionary to the entire physical first matrix. -/
theorem assemble_completed_rows (net : Network 4 6 5)
    (A : Fin 4 → Point 4) (i : Fin 4) (e : Fin 4 ≃ invariantRows net)
    (ρ : Fin 4 → ℝ) (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (hrows : ∀ j, net.W₁ (e j).val = ρ j • (fun k => A j (q k)))
    (p n : Fin 6) (cp cm : ℝ) (hpn : p ≠ n) (hcp : 0 < cp) (hcm : 0 < cm)
    (hp : net.W₁ p = cp • (fun k => unitVec i (q k)))
    (hn : net.W₁ n = cm • (fun k => (-unitVec i) (q k)))
    (hother : ∀ j, (∑ k, net.W₁ j k) = 0 ↔ j ≠ p ∧ j ≠ n) :
    ∃ P : Equiv.Perm (Fin 6), ∃ s : Fin 6 → ℝ,
      (∀ j, 0 < s j) ∧
      ∀ j, net.W₁ (P j) = s j • (fun k => completedRows A i j (q k)) := by
  classical
  let f : Fin 6 → Fin 6 := Fin.append (fun j => (e j).val) ![p,n]
  let P : Equiv.Perm (Fin 6) := Equiv.ofBijective f
    (invariant_carrier_enumeration_bijective net e p n hpn hother)
  let s : Fin 6 → ℝ := Fin.append ρ ![cp,cm]
  refine ⟨P,s,?_,?_⟩
  · intro j
    refine Fin.addCases (m := 4) (n := 2) (motive := fun j : Fin 6 => 0 < s j)
      (fun j => ?_) (fun j => ?_) j
    · simpa only [s,Fin.append_left] using hρ j
    · simp only [s,Fin.append_right]
      fin_cases j
      · exact hcp
      · exact hcm
  · intro j
    refine Fin.addCases (m := 4) (n := 2)
      (motive := fun j : Fin 6 => net.W₁ (P j) = s j • (fun k => completedRows A i j (q k)))
      (fun j => ?_) (fun j => ?_) j
    · change net.W₁ (f (Fin.castAdd 2 j)) = _
      simpa only [f,s,completedRows,Fin.append_left] using hrows j
    · change net.W₁ (f (Fin.natAdd 4 j)) = _
      simp only [f,s,completedRows,Fin.append_right]
      fin_cases j
      · exact hp
      · exact hn

/-- The full six-row normal form is a conclusion from the actual network,
its four invariant rows, and a canonical point with all four features inactive.
All original biases and all physical second-layer parameters remain free. -/
theorem completed_rows_of_inactive_frame (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (A : Fin 4 → Point 4) (e : Fin 4 ≃ invariantRows net)
    (ρ : Fin 4 → ℝ) (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (hrows : ∀ j, net.W₁ (e j).val = ρ j • (fun k => A j (q k)))
    (i : Fin 4) (z : Point 4) (hz : z i = Maximum 4 z)
    (hinactive : ∀ j, lin (A j) z < 0) :
    ∃ P : Equiv.Perm (Fin 6), ∃ s : Fin 6 → ℝ,
      (∀ j, 0 < s j) ∧
      ∀ j, net.W₁ (P j) = s j • (fun k => completedRows A i j (q k)) := by
  classical
  have hcard : (Finset.univ.filter fun j => (∑ k, net.W₁ j k) = 0).card = 4 := by
    have he := Fintype.card_congr e
    simpa only [Fintype.card_fin,Fintype.card_coe,invariantRows] using he.symm
  let x : Point 4 := fun k => z (q k)
  have hx : x (q.symm i) = Maximum 4 x := by
    change z (q (q.symm i)) = Maximum 4 (fun k => z (q k))
    rw [q.apply_symm_apply,maximum_permute q z,hz]
  have hactual : ∀ j, (∑ k, net.W₁ j k) = 0 → lin (net.W₁ j) x < 0 := by
    intro j hj
    have hjm : j ∈ invariantRows net := by
      simpa only [invariantRows,Finset.mem_filter,Finset.mem_univ,true_and] using hj
    let k : Fin 4 := e.symm ⟨j,hjm⟩
    have hek : (e k).val = j := congrArg Subtype.val (e.apply_symm_apply ⟨j,hjm⟩)
    rw [← hek,hrows k,lin_smul_left]
    have hlin : lin (fun l => A k (q l)) x = lin (A k) z := by
      exact Fintype.sum_equiv q _ _ (fun l => rfl)
    rw [hlin]
    exact mul_neg_of_pos_of_neg (hρ k) (hinactive k)
  obtain ⟨p,n,cp,cm,hpn,hcp,hcm,hp,hn,hother⟩ :=
    coordinate_carrier_completion net hnet hcard (q.symm i) x hx hactual
  have hunit : unitVec (q.symm i) = (fun k => unitVec i (q k)) := by
    funext k
    simp only [unitVec,q.eq_symm_apply]
  apply assemble_completed_rows net A i e ρ q hρ hrows p n cp cm hpn hcp hcm _ _ hother
  · simpa only [hunit] using hp
  · simpa only [hunit,Pi.neg_apply] using hn

#print axioms invariant_carrier_enumeration_bijective
#print axioms assemble_completed_rows
#print axioms completed_rows_of_inactive_frame
end MaxCaterpillar.Fiber.Count65.FrameTransport
