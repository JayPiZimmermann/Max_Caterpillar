import MaxCaterpillar.Fiber.Count65.Paired.Carrier
import MaxCaterpillar.Fiber.Count65.Paired.PhysicalAtoms
import MaxCaterpillar.Fiber.Count65.Paired.Absorption

/-! # Globally nonnegative physical carrier extracted from four effective atoms -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier

lemma paired_physical_preact (W : Fin 6 → ℝ) (U : Fin 2 → Fin 2 → ℝ)
    (x : Point 4) :
    Absorption.preact (pairedRows U) 0 W 0 x =
      codeIntercept (fun _ : Fin 1 => W) U (x 1) (x 3) 0+
        W 0*relu (x 0-x 1)+W 1*relu (x 2-x 3) := by
  simp only [Absorption.preact, Pi.zero_apply,add_zero]
  have hrow : ∀ j, (∑ i, pairedRows U j i*x i) =
      (![x 0-x 1,x 2-x 3,U 0 0*x 1+U 0 1*x 3,
        -(U 0 0*x 1+U 0 1*x 3),U 1 0*x 1+U 1 1*x 3,
        -(U 1 0*x 1+U 1 1*x 3)] : Fin 6 → ℝ) j := by
    intro j
    fin_cases j <;> simp [pairedRows,Fin.sum_univ_succ,
      show (Fin.succ (2 : Fin 3) : Fin 4)=3 from rfl] <;> ring
  simp_rw [hrow]
  simp only [codeIntercept,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]
  norm_num [Fin.succ,Fin.ofNat,Fin.ofNat']
  simp only [show (⟨2,by decide⟩ : Fin 6)=2 from rfl,
    show (⟨3,by decide⟩ : Fin 6)=3 from rfl,
    show (⟨4,by decide⟩ : Fin 6)=4 from rfl,
    show (⟨5,by decide⟩ : Fin 6)=5 from rfl]
  ring

/-- Four active scalar atoms in an actual exact network force a genuine
physical second preactivation nonnegative on every real input. -/
theorem network_four_atoms_unique_carrier (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x, net.eval x=Maximum 4 x)
    (hfour : (activeAtoms net.w₃ (fun k => net.W₂ k 0)
      (fun k => net.W₂ k 1)).card=4) :
    ∃ k, 0<net.W₂ k 0+net.W₂ k 1 ∧ 0<net.w₃ k ∧
      (∀ i, i≠k → net.W₂ i 0+net.W₂ i 1=0 ∧ net.W₂ i 0≠0 ∧ net.w₃ i≠0) ∧
      (∀ x, 0≤Absorption.preact net.W₁ net.b₁ (net.W₂ k) (net.b₂ k) x) := by
  have hh := network_two_increment_identity net U hU hb hnet 0 0
  obtain ⟨k,hk,hd,hrest,_⟩ := four_atoms_force_unique_carrier 0 0 net.w₃
    (codeIntercept net.W₂ U 0 0) (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)
    hh hfour
  refine ⟨k,hk,hd,hrest,?_⟩
  intro x
  have hp := (unique_carrier_positive (x 1) (x 3) net.w₃
    (codeIntercept net.W₂ U (x 1) (x 3)) (fun k => net.W₂ k 0)
    (fun k => net.W₂ k 1) (network_two_increment_identity net U hU hb hnet _ _)
    k hk (fun i hi => (hrest i hi).1)).2
      (relu (x 0-x 1)) (relu (x 2-x 3)) (relu_nonneg _) (relu_nonneg _)
  rcases hb with ⟨hb₁,hb₂,_⟩
  rw [hU,hb₁,hb₂,Pi.zero_apply,paired_physical_preact]
  exact hp

end MaxCaterpillar.Fiber.Count65.Paired
